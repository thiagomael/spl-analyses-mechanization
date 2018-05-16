-- The purpose of this theory is to model the essential concepts and behavior regarding
-- analysis of non-variable and variable models. We first present definitions regarding 
-- non-variable models, then definitions for variable ones. 
-- Ultimately, we aim at deriving the latter from the former.
module SPLTheory where
import Prelude hiding (pi)

------ Non-variable definitions

-- A non-variable model is either a basic non-dividable construct or a nested structure
-- later on, the nesting could be considered as a list, or a normal form approach could be taken.
-- The initial spec and verification in PVS might be simpler with the current version below.
data Product = Basic |                
               Composite Product Product

data Property = SomeValue;

-- Function operating on intermediate results during the analysis of non-variable models.
-- The idea is that this function provides a high-level view of the analysis function,
-- i.e., modulo the structural recursion.
type  AnalyzeModelCompositeShell = Property -> Property -> Property

analyzeModelCompositeShell :: AnalyzeModelCompositeShell 
analyzeModelCompositeShell _ _ = SomeValue

-- To analyze a non-variable model, we return some uninterpreted value in the basic case 
-- or apply an analysis shell function to the intemediate results emerging from the recursive application
-- in the nested structure of the model 
alpha :: Product -> Property
alpha Basic = SomeValue
alpha (Composite m1 m2) =  analyzeModelCompositeShell (alpha m1) (alpha m2)

------ variable definitions

-- a presence condition is a feature expression, yet to detail
data PresenceCondition;

-- A configuration values a presence condition 
type Conf = PresenceCondition -> Bool

-- A variable model is either a base non-variable model, a variation point with choices depending on an option,
-- or a nested variant structure
data AnnotativeModel = ModelBase Product | 
                       ModelChoice PresenceCondition AnnotativeModel AnnotativeModel |
                       ModelComposite  AnnotativeModel  AnnotativeModel

-- The following function binds variability in a variable model for a given configuration via structural recursion.
-- In case the model has no variability, the base model is returned. Otherwise, in case of a variation point,
-- the derivation continues within the choice corresponding to the configuration. In case of a composite variable model, 
-- a composite non-variable model is returned after binding the internal structure.
pi :: AnnotativeModel -> Conf -> Product
pi (ModelBase m) _ = m
pi (ModelChoice pc vm1 vm2) c = if c pc 
                                   then pi vm1 c 
                                   else pi vm2 c
pi (ModelComposite vm1 vm2) c = Composite (pi vm1 c)  (pi vm2 c)
				
-- Representation of variability bookeeping of analysis. This supports lazy computation of the analysis				
data AnnotativeExpression = BaseExpression Property | 
                            ChoiceExpression PresenceCondition AnnotativeExpression AnnotativeExpression | 
                            CompositeExpression AnalyzeModelCompositeShell AnnotativeExpression  AnnotativeExpression ;  

-- Binds the variability in the variability bookeeping of analysis
sigma :: AnnotativeExpression -> Conf -> Property
sigma (BaseExpression p) _ = p
sigma (ChoiceExpression pc vp1 vp2) c = if (c pc) then (sigma vp1 c) else (sigma vp2 c)
sigma (CompositeExpression analysisShell vp1 vp2) c =  analysisShell (sigma vp1 c) (sigma vp2 c)

-- Analyzes a variable model via structural recursion. In case the model has no variability, the non-variable 
-- analysis is performed. Otherwise, variability bookeeping is performed considering the structure of variability.
hatAlpha :: AnnotativeModel -> AnnotativeExpression
hatAlpha (ModelBase m) = BaseExpression (alpha m)
hatAlpha (ModelChoice pc vm1 vm2) = ChoiceExpression pc (hatAlpha vm1) (hatAlpha vm2)
hatAlpha (ModelComposite vm1 vm2) = CompositeExpression analyzeModelCompositeShell(hatAlpha vm1) (hatAlpha vm2)
