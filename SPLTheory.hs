{- The purpose of this theory is to model the essential concepts on the analysis 
   of variable models. We first present definitions regarding 
   non-variable models, then definitions for variable ones, which bild on the former. 
   Ultimately, we aim at deriving the latter from the former. -}
   
module SPLTheory where
import Prelude hiding (pi)

------ Non-variable definitions  *** Central part of the diagram ***

-- A non-variable model is an uninterpreted type abstracting the details of any particular product type
data Product = SomeProduct;

data Property = SomeValue deriving Eq

{- To analyze a non-variable model, we return some uninterpreted value since the analysis is given
 In other words, since the non-variable  model is uninterpreted, so is its analysis.-}
alpha :: Product -> Property
alpha _  = SomeValue

------ variable definitions >>>>*** top-right quadrant of the diagram ***<<<<

-- A presence condition is a feature expression, uninterpreted at the moment.
data PresenceCondition = SomeCondition deriving Eq

-- A configuration values a presence condition 
type Conf = PresenceCondition -> Bool  

{- Like in the Choice Calculus, a generic variable structure is either a non-variable model or a variation point 
   with choices depending on an option. -}
data V a = Base a |
           Choice PresenceCondition (V a) (V a)

{- The following function binds variability in a generic variable  structure for a given configuration via structural recursion.
   In case the structure has no variability, the base structure is returned. Otherwise, in case of a variation point,
   the derivation continues within the choice corresponding to the configuration. -} 
           
derivation :: V a-> Conf -> a

derivation (Base e) _ = e 
derivation (Choice pc vm1 vm2) c = if c pc 
                                    then derivation vm1 c 
                                    else derivation vm2 c

type AnnotativeModel =  V Product

-- binding variability in an annotative model is derivation of that model for a given configuration
pi :: AnnotativeModel -> Conf -> Product
pi am c = derivation am c
                
type AnnotativeExpression = V Property                
                       
-- like pi, binding variability in an annotative expression is derivation of that expression for a given configuration
sigma :: AnnotativeExpression -> Conf -> Property
sigma ae c = derivation ae c 

{- hatAlpha analyzes a variable model via structural recursion. In case the model has no variability, the non-variable 
   analysis is performed. Otherwise, variability is preserved in the emerging expression. In other words, hatAlpha
   maps alpha over the V functor with a concret implementation.-}

hatAlpha :: AnnotativeModel -> AnnotativeExpression
hatAlpha am = fmap alpha am 

instance Functor V where
  fmap f (Base m) = Base (f m)
  fmap f (Choice pc m1 m2) = Choice pc (fmap f m1) (fmap f m2)

-- specifying top-right quadrant commutativity
commutative_product_family_product :: Conf -> AnnotativeModel -> Bool
commutative_product_family_product conf  vModel = sigma (hatAlpha vModel) conf ==  alpha(pi vModel conf)


-- >>>>*** top-left quadrant of the diagram, including variability encoding ***<<<<

-- auxiliary definitions for  variability encoding and binding variabiliy in compositional models
type LocalVariability u = PresenceCondition -> V u -> V u ->  V u

bindLocal :: Conf -> LocalVariability u 
bindLocal c pc t e  = if (c pc) then t else e 

encodeChoice :: LocalVariability u 
encodeChoice pc t e  = Choice pc t e

{- to either bind or encode variability in compositional models, basic behavior is needed for the composition of elements 
   in each node of the relation incorporating dependent elements from the recursive composition along the structure -}

type PartialComposition a =  V a -> V a -> V a

-- binding the composition mechanims for models, semantically constrained by the assumption below
partialModelComposition ::  PartialComposition Product

--dummy implementation. In PVS, the function would remain uninterpreted
partialModelComposition am p = am

-- binding the composition mechanims for property, semantically constrained by the assumption below
partialExpComposition :: PartialComposition Property

--dummy implementation. In PVS, partialComposition would remain uninterpreted  
partialExpComposition ae e = ae


{- *****ASSUMPTION to be encoded in PVS: **** really needed ??? intuitively, this is some kind of local assumption
   hatAlpha (partialModelComposition m1 m2 ) = partialExpComposition (hatAlpha m1) (hatAlpha m2)
   This assumption establishes an hatAlpha as a monomorphism between AnnotativeModel and AnnotativeExpression
   in which the respective morphisms involve the partial composition operations. In short, the assumption is
   that partial composition of models and expressions must preserve the correspondence between models and 
   expressions established by the analysis function. This will probably by needed in the proof of the commuitative 
   property for this quadrant.    Hint: the definitions of pi' and sigma' below are quite similar -}

--assumption :: AnnotativeModel -> AnnotativeModel -> Bool
--assumption m1 m2 = hatAlpha (partialModelComposition m1 m2 ) == partialExpComposition (hatAlpha m1) (hatAlpha m2)

-- a well-founded functor has a top element and dependents of a given node.
class (Functor t) => WellFoundedFunctor t where 
   top :: t u -> u
   dependents :: t u ->  u -> [(PresenceCondition, t u)]
  
-- a CompositionalModel is a well-founded functor   
class (WellFoundedFunctor t) =>  CompositionalModel t where 
{- To smash a compositional variational entity cs into a plain variational entity, we fold partialComposition along the 
 well-founded relation induced by the structure of cs. The local handling of the dependencies is paramaterized in f, as
 explored by variability encoding and binding functions pi' and sigma'. d is the feature disabler.-}
   
   smash ::  t (V u) ->  PartialComposition u -> LocalVariability u -> u -> V u
   smash  cs partialComposition f d =  foldl partialComposition 
                                             (top cs) 
                                             (map (\(pc,scs) -> (let rt = (smash scs partialComposition f d)
                                                                     re = (Base d)  in  
                                                                   f pc rt re )) 
                                                  (dependents cs (top cs))) 
                                                             
   pi' :: Conf -> t AnnotativeModel ->  Product
   pi' c cm =  let Base r = (smash cm partialModelComposition  (bindLocal c)  SomeProduct) in r
   
   sigma' :: Conf -> t AnnotativeExpression -> Property  
   sigma' c ce = let Base r = (smash ce partialExpComposition (bindLocal c) SomeValue) in r 

   -- variability encoding of compositional models into annotative models
   vEncM ::  t AnnotativeModel -> PartialComposition Product -> AnnotativeModel
   vEncM cm  partialModelComposition = smash cm partialModelComposition encodeChoice  SomeProduct
   
   -- variability encoding of compositional expressions into annotative expressions
   vEncP ::  t AnnotativeExpression -> PartialComposition Property -> AnnotativeExpression
   vEncP ce  partialExpComposition = smash ce partialExpComposition encodeChoice SomeValue
      
   -- biding of compositional models via variability encoding
   pi'' :: Conf -> t AnnotativeModel ->  Product
   pi'' c cm =  pi (vEncM cm  partialModelComposition) c 
   
   -- biding of compositional expressions via variability encoding
   sigma'' :: Conf -> t AnnotativeExpression -> Property  
   sigma'' c ce = sigma (vEncP ce partialExpComposition ) c

  {- The analysis of a compositional model maps the the variability-aware unstructured analysis hatAlpha
     over the structure of the model -}
   analyzeCM ::  t AnnotativeModel -> t AnnotativeExpression
   analyzeCM cm = fmap hatAlpha cm 
   
   commutative_feature_product_product ::  Conf -> t AnnotativeModel -> Bool
   commutative_feature_product_product conf  cModel = sigma' conf (analyzeCM cModel)  ==  alpha(pi' conf cModel )
