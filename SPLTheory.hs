module SPLTheory where


data Model;
data Property = SomeValue;
data Option;
type Conf = Option -> Bool

data VarModel = ModelBase Model | ModelChoice Option VarModel VarModel;
data VarProperty = PropertyBase Property | PropertyChoice Option VarProperty VarProperty;


varJoinProperty :: Option -> VarProperty -> VarProperty -> VarProperty
varJoinProperty o vp1 vp2 = PropertyChoice o vp1 vp2

projectProperty :: VarProperty -> Conf -> Property
projectProperty (PropertyChoice o vp1 vp2) c = if c o then projectProperty vp1 c else projectProperty vp2 c
projectProperty (PropertyBase p) _ = p

projectModel :: VarModel -> Conf -> Model
projectModel (ModelChoice o vm1 vm2) c = if c o then projectModel vm1 c else projectModel vm2 c
projectModel (ModelBase m) _ = m

analyzeModel :: Model -> Property
analyzeModel _ = SomeValue

varAnalyzeModel :: VarModel -> VarProperty
varAnalyzeModel (ModelBase m) = PropertyBase (analyzeModel m)
varAnalyzeModel (ModelChoice o vm1 vm2) = varJoinProperty o (varAnalyzeModel vm1) (varAnalyzeModel vm2)