-- The purpose of this theory is to model the essential concepts and behavior regarding
-- analysis of non-variable and variable models. We first present definitions regarding 
-- non-variable models, then definitions for variable ones. 
-- Ultimately, we aim at deriving the latter from the former.
module SPLTheory where

------ Non-variable definitions

-- A non-variable model is either a basic non-dividable construct or a nested structure
-- later on, the nesting could be considered as a list, or a normal form approach could be taken.
-- The initial spec and verification in PVS might be simpler with the current version below.
data Model = Basic |                
             Composite Model Model 

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
analyzeModel :: Model -> Property
analyzeModel Basic = SomeValue
analyzeModel (Composite m1 m2) =  analyzeModelCompositeShell (analyzeModel  m1) (analyzeModel  m2)


------ variable definitions

-- a feature is a configuration option
data Option;

-- A configuration is a feature selection
type Conf = Option -> Bool

-- A variable model is either a base non-variable model, a variation point with choices depending on an option,
-- or a nested variant structure
data VarModel = ModelBase Model | 
                ModelChoice Option VarModel VarModel |
                ModelComposite   VarModel  VarModel

-- The following function binds variability in a variable model for a given configuration via structural recursion.
-- In case the model has no variability, the base model is returned. Otherwise, in case of a variation point,
-- the derivation continues within the choice corresponding to the configuration. In case of a composite variable model, 
-- a composite non-variable model is returned after binding the internal structure.
projectModel :: VarModel -> Conf -> Model
projectModel (ModelBase m) _ = m
projectModel (ModelChoice o vm1 vm2) c = if c o then projectModel vm1 c else projectModel vm2 c
projectModel (ModelComposite vm1 vm2) c = Composite (projectModel vm1 c)  (projectModel vm2 c)
				
-- Representation of variability bookeeping of analysis. This supports lazy computation of the analysis				
data VarProperty = PropertyBase Property | 
                   PropertyChoice Option VarProperty VarProperty | 
                   PropertyComposite AnalyzeModelCompositeShell VarProperty  VarProperty ;  

-- Performs variability bookeeping of analysis for variation points				
varJoinProperty :: Option -> VarProperty -> VarProperty -> VarProperty
varJoinProperty o vp1 vp2 = PropertyChoice o vp1 vp2

-- Performs variability bookeeping of analysis for composite structures				
varCompositeProperty ::  VarProperty -> VarProperty -> VarProperty
varCompositeProperty vp1 vp2 = PropertyComposite analyzeModelCompositeShell vp1 vp2

-- Binds the variability in the variability bookeeping of analysis
projectProperty :: VarProperty -> Conf -> Property
projectProperty (PropertyBase p) _ = p
projectProperty (PropertyChoice o vp1 vp2) c = if c o then projectProperty vp1 c else projectProperty vp2 c
projectProperty (PropertyComposite analysisShell vp1 vp2) c =  analysisShell (projectProperty vp1 c) (projectProperty vp2 c)

-- Analyzes a variable model via structural recursion. In case the model has no variability, the non-variable 
-- analysis is performed. Otherwise, variability bookeeping is performed considering the structure of variability.
varAnalyzeModel :: VarModel -> VarProperty
varAnalyzeModel (ModelBase m) = PropertyBase (analyzeModel m)
varAnalyzeModel (ModelChoice o vm1 vm2) = varJoinProperty o (varAnalyzeModel vm1) (varAnalyzeModel vm2)
varAnalyzeModel (ModelComposite vm1 vm2) = varCompositeProperty (varAnalyzeModel vm1) (varAnalyzeModel vm2)
