-- The purpose of this theory is to model the essential concepts and behavior regarding
-- analysis of non-variable and variable models. We first present definitions regarding 
-- non-variable models, then definitions for variable ones. 
-- Ultimately, we aim at deriving the latter from the former.
module SPLTheory where
import Prelude hiding (pi)

------ Non-variable definitions

-- A non-variable model is an uninterpreted type abstracting the details of any particular product type
data Product;

data Property = SomeValue deriving Eq

-- To analyze a non-variable model, we return some uninterpreted value since the analysis is given
-- In other words, since the non-variable  model is uninterpreted, so is its analysis.
alpha :: Product -> Property
alpha _  = SomeValue

------ variable definitions

-- a presence condition is a feature expression, yet to detail
data PresenceCondition;

-- A configuration values a presence condition 
type Conf = PresenceCondition -> Bool  

-- A variable model is either a non-variable model or a variation point with choices depending on an option,
data AnnotativeModel = ModelBase Product | 
                       ModelChoice PresenceCondition AnnotativeModel AnnotativeModel 
                       

-- The following function binds variability in a variable model for a given configuration via structural recursion.
-- In case the model has no variability, the base model is returned. Otherwise, in case of a variation point,
-- the derivation continues within the choice corresponding to the configuration. 
pi :: AnnotativeModel -> Conf -> Product
pi (ModelBase m) _ = m
pi (ModelChoice pc vm1 vm2) c = if c pc 
                                   then pi vm1 c 
                                   else pi vm2 c

                
-- Representation of variability bookeeping of analysis. This supports lazy computation of the analysis             
data AnnotativeExpression = BaseExpression Property | 
                            ChoiceExpression PresenceCondition AnnotativeExpression AnnotativeExpression 
                            

-- Binds the variability in the variability bookeeping of analysis
sigma :: AnnotativeExpression -> Conf -> Property
sigma (BaseExpression p) _ = p
sigma (ChoiceExpression pc vp1 vp2) c = if (c pc) then (sigma vp1 c) else (sigma vp2 c)

-- Analyzes a variable model via structural recursion. In case the model has no variability, the non-variable 
-- analysis is performed. Otherwise, variability bookeeping is performed considering the structure of variability.
hatAlpha :: AnnotativeModel -> AnnotativeExpression
hatAlpha (ModelBase m) = BaseExpression (alpha m)
hatAlpha (ModelChoice pc vm1 vm2) = ChoiceExpression pc (hatAlpha vm1) (hatAlpha vm2)


-- specifying top-right quadrant commutativity
--conf: VAR Conf
--vModel : VAR AnnotativeModel
--commutative_product_family_product: THEOREM sigma(hatAlpha(vModel),conf) = alpha(pi(vModel,conf))

commutative_product_family_product :: Conf -> AnnotativeModel -> Bool

commutative_product_family_product conf  vModel = sigma (hatAlpha vModel) conf ==  alpha(pi vModel conf)

