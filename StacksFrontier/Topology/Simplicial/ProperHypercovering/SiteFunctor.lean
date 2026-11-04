module

public import StacksFrontier.Topology.Simplicial.ProperHypercovering.QcTotalSite
public import StacksFrontier.Topology.Simplicial.Site

/-!
# The comparison morphism `Sh((LC_qc/U)_total) → Sh(U_Zar)`

Let `U` be a simplicial object of the quasi-compact site `LC_qc` and `a : U → X` an augmentation.
The underlying simplicial topological space of `U` has the site `U_Zar` of simplicial opens, and
an open `V ⊆ U_n` in simplicial degree `n`, viewed as the open immersion `V → U_n`, is an object
`V/U_n` of the total site `(LC_qc/U)_total`. This is the functor

`U_Zar → (LC_qc/U)_total`, `V ↦ V/U_n`,

which in each simplicial degree is the open-subset functor `U_{n,Zar} → LC_qc/U_n` of
Cohomology on Sites, Section 21.31. It is representably flat and cover-preserving, hence
continuous, and so defines a morphism of topoi

`h : Sh((LC_qc/U)_total) → Sh(U_Zar)`

whose direct image is restriction along it.

## Main definitions

* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.simplicialSpace`: the simplicial
  topological space underlying `U`, and `spaceAugmentation` the augmentation it inherits.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.opensFactor`: the factorization of a map
  through an open subspace containing its image.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.siteFunctor`: the functor `V ↦ V/U_n`.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.totalComparisonMorphism`: the morphism of
  topoi `h`.

## Main results

* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.siteFunctor_representablyFlat` and
  `siteFunctor_isContinuous`: the functor `V ↦ V/U_n` is representably flat and continuous.

## References

* [Stacks Project, Tag 0DAF](https://stacks.math.columbia.edu/tag/0DAF)
* [Stacks Project, Section 21.31 (Tag 09WY)](https://stacks.math.columbia.edu/tag/09WY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.SemiRepresentable.Simplicial
open Stacks.CategoryTheory.Hypercovering Stacks.Topology.Simplicial

universe x u w

namespace Stacks.Topology.LocallyQuasiCompactZariskiSituation

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}
  (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound)

/-- The underlying topological space of an object of the site. -/
abbrev toTop : S.category ⥤ TopCat.{u} :=
  S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop

/-- Passing to the underlying topological space is fully faithful on the site. -/
def toTopFullyFaithful : (toTop S).FullyFaithful :=
  (ObjectProperty.fullyFaithfulι _).comp (ObjectProperty.fullyFaithfulι _)

section OpensLift

variable {S} (Y : S.category) (V : Opens Y.obj)

/-- The open immersion `V → Y` attached to an open subset is a monomorphism of the site. -/
instance instMonoOpensToSliceHom : Mono ((S.opensToSlice Y).1.obj V).hom :=
  ConcreteCategory.mono_of_injective _ ((S.opensToSlice Y).2 V).1.injective

/-- Two maps into an open subspace agree as soon as they agree after the open immersion. -/
theorem opensToSlice_hom_ext {Z : S.category} {f g : Z ⟶ ((S.opensToSlice Y).1.obj V).left}
    (h : f ≫ ((S.opensToSlice Y).1.obj V).hom = g ≫ ((S.opensToSlice Y).1.obj V).hom) :
    f = g :=
  (cancel_mono _).1 h

/-- A map which factors through an open subspace has its image in that open subset. -/
theorem mem_of_factors {Z : S.category} (f : Z ⟶ ((S.opensToSlice Y).1.obj V).left)
    (z : Z.obj) : (f ≫ ((S.opensToSlice Y).1.obj V).hom) z ∈ V := by
  have h := ((S.opensToSlice Y).2 V).2
  show _ ∈ V.1
  rw [← h]
  exact ⟨f z, rfl⟩

/-- A map `Z → Y` whose image lies in an open subset `V` has every value in the image of the open
immersion `V → Y`. -/
theorem opensFactor_exists {Z : S.category} (g : Z ⟶ Y) (hg : ∀ z : Z.obj, g z ∈ V)
    (z : Z.obj) : ∃ y : ((S.opensToSlice Y).1.obj V).left.obj,
      ((S.opensToSlice Y).1.obj V).hom y = g z := by
  have h := ((S.opensToSlice Y).2 V).2
  have hz : g z ∈ V.1 := hg z
  rw [← h] at hz
  exact hz

/-- The function underlying the factorization of a map through an open subspace containing its
image. -/
def opensFactorFun {Z : S.category} (g : Z ⟶ Y) (hg : ∀ z : Z.obj, g z ∈ V) :
    Z.obj → ((S.opensToSlice Y).1.obj V).left.obj :=
  fun z => (opensFactor_exists Y V g hg z).choose

/-- The function `opensFactorFun Y V g hg` followed by the open immersion `V → Y` is `g`. -/
theorem opensFactorFun_spec {Z : S.category} (g : Z ⟶ Y) (hg : ∀ z : Z.obj, g z ∈ V)
    (z : Z.obj) : ((S.opensToSlice Y).1.obj V).hom (opensFactorFun Y V g hg z) = g z :=
  (opensFactor_exists Y V g hg z).choose_spec

/-- The function `opensFactorFun` is continuous. -/
theorem continuous_opensFactorFun {Z : S.category} (g : Z ⟶ Y) (hg : ∀ z : Z.obj, g z ∈ V) :
    Continuous (opensFactorFun Y V g hg) := by
  rw [((S.opensToSlice Y).2 V).1.isEmbedding.continuous_iff]
  have : (((S.opensToSlice Y).1.obj V).hom : _ → Y.obj) ∘ opensFactorFun Y V g hg = g :=
    funext (opensFactorFun_spec Y V g hg)
  rw [this]
  exact (ConcreteCategory.hom ((toTop S).map g)).continuous

/-- The factorization of a map through an open subspace containing its image, on underlying
spaces. -/
def opensFactorTop {Z : S.category} (g : Z ⟶ Y) (hg : ∀ z : Z.obj, g z ∈ V) :
    (toTop S).obj Z ⟶ (toTop S).obj ((S.opensToSlice Y).1.obj V).left :=
  TopCat.ofHom ⟨opensFactorFun Y V g hg, continuous_opensFactorFun Y V g hg⟩

/-- A map `Z → Y` whose image lies in an open subset `V` factors through the open subspace
`V`. -/
def opensFactor {Z : S.category} (g : Z ⟶ Y) (hg : ∀ z : Z.obj, g z ∈ V) :
    Z ⟶ ((S.opensToSlice Y).1.obj V).left :=
  (toTopFullyFaithful S).preimage (opensFactorTop Y V g hg)

/-- The factorization through an open subspace is a factorization. -/
@[reassoc (attr := simp)]
theorem opensFactor_comp {Z : S.category} (g : Z ⟶ Y) (hg : ∀ z : Z.obj, g z ∈ V) :
    opensFactor Y V g hg ≫ ((S.opensToSlice Y).1.obj V).hom = g := by
  apply (toTopFullyFaithful S).map_injective
  rw [Functor.map_comp, opensFactor, Functor.FullyFaithful.map_preimage]
  ext z
  exact opensFactorFun_spec Y V g hg z

end OpensLift

variable (U : SimplicialObject S.category) {X : S.category}
  (a : U ⟶ (SimplicialObject.const S.category).obj X)

/-- The simplicial topological space underlying a simplicial object of the site. Its site of
simplicial opens is the site `U_Zar`. -/
abbrev simplicialSpace : SimplicialObject TopCat.{u} := U ⋙ toTop S

/-- The augmentation `a : U → X`, read as an augmentation of simplicial topological spaces. -/
abbrev spaceAugmentation :
    simplicialSpace S U ⟶ (SimplicialObject.const TopCat).obj ((toTop S).obj X) :=
  Functor.whiskerRight a (toTop S)

/-- The open immersion `V → U_n` attached to a simplicial open `V ⊆ U_n`, as an object over
`U_n`. -/
abbrev simplicialOpenSlice (P : SimplicialOpen (simplicialSpace S U)) : Over (U.obj P.degree) :=
  (S.opensToSlice (U.obj P.degree)).1.obj P.toOpens

variable {S U}

/-- The augmentation commutes with the simplicial structure maps. -/
@[reassoc (attr := simp)]
theorem augmentation_naturality {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m) :
    U.map φ ≫ a.app m = a.app n := by
  simp

variable (S U)

/-- The object `V/U_n` of `(LC_qc/U)_total` attached to an open `V ⊆ U_n` in simplicial degree
`n`. -/
abbrev siteFunctorObj (P : SimplicialOpen (simplicialSpace S U)) : qcTotal.{x} S U a where
  left := ⟨(simplicialOpenSlice S U P).left, ⟨⟨⟩⟩,
    (simplicialOpenSlice S U P).hom ≫ a.app P.degree⟩
  right := P.degree
  hom := (FormalCoproduct.incl (Over X)).map
    (Over.homMk (simplicialOpenSlice S U P).hom : _ ⟶ (Over.lift U a).obj P.degree)

/-- The map of open subspaces underlying a morphism of simplicial opens. -/
def siteFunctorMapLeft {P Q : SimplicialOpen (simplicialSpace S U)} (f : P ⟶ Q) :
    (simplicialOpenSlice S U P).left ⟶ (simplicialOpenSlice S U Q).left :=
  opensFactor (U.obj Q.degree) Q.toOpens ((simplicialOpenSlice S U P).hom ≫ U.map f.base)
    (fun z => SimplicialOpen.Hom.le f (mem_of_factors (U.obj P.degree) P.toOpens (𝟙 _) z))

/-- The map `siteFunctorMapLeft f` of open subspaces commutes with the open immersions and the
simplicial structure map of `f`. -/
@[reassoc (attr := simp)]
theorem siteFunctorMapLeft_comp {P Q : SimplicialOpen (simplicialSpace S U)} (f : P ⟶ Q) :
    siteFunctorMapLeft S U f ≫ (simplicialOpenSlice S U Q).hom =
      (simplicialOpenSlice S U P).hom ≫ U.map f.base :=
  opensFactor_comp (U.obj Q.degree) Q.toOpens _ _

/-- The functor `U_Zar → (LC_qc/U)_total` taking an open `V ⊆ U_n` in simplicial degree `n` to
the object `V/U_n`. -/
def siteFunctor : SimplicialOpen (simplicialSpace S U) ⥤ qcTotal.{x} S U a where
  obj P := siteFunctorObj.{x} S U a P
  map {P Q} f :=
    { left := Over.homMk (siteFunctorMapLeft S U f) (by
        dsimp [siteFunctorObj]
        rw [siteFunctorMapLeft_comp_assoc, augmentation_naturality])
      right := f.base
      w := by
        dsimp [siteFunctorObj]
        rw [← Functor.map_comp, ← Functor.map_comp]
        congr 1
        apply Over.OverMorphism.ext
        simp only [Over.comp_left, Over.homMk_left]
        exact siteFunctorMapLeft_comp S U f }
  map_id P := by
    apply Comma.hom_ext
    · apply Over.OverMorphism.ext
      apply opensToSlice_hom_ext
      change siteFunctorMapLeft S U (𝟙 P) ≫ _ = 𝟙 _ ≫ _
      rw [siteFunctorMapLeft_comp]
      change _ ≫ U.map (𝟙 P.degree) = _
      simp
    · rfl
  map_comp f g := by
    apply Comma.hom_ext
    · apply Over.OverMorphism.ext
      apply opensToSlice_hom_ext
      change siteFunctorMapLeft S U (f ≫ g) ≫ _ =
        (siteFunctorMapLeft S U f ≫ siteFunctorMapLeft S U g) ≫ _
      rw [Category.assoc, siteFunctorMapLeft_comp, siteFunctorMapLeft_comp,
        siteFunctorMapLeft_comp_assoc]
      change _ ≫ U.map (f.base ≫ g.base) = _
      simp
    · rfl

variable {S U a}

/-- The structural morphism `V → U_n` over `X` of an object `V/U_n` of `(LC_qc/U)_total`. -/
def structureHom (Z : qcTotal.{x} S U a) : Z.left ⟶ (Over.lift U a).obj Z.right :=
  (FormalCoproduct.fullyFaithfulIncl (C := Over X)).preimage Z.hom

/-- The structural morphism `structureHom Z`, included into formal coproducts, is the structure
morphism of `Z`. -/
theorem incl_map_structureHom (Z : qcTotal.{x} S U a) :
    (FormalCoproduct.incl (Over X)).map (structureHom Z) = Z.hom :=
  (FormalCoproduct.fullyFaithfulIncl (C := Over X)).map_preimage _

/-- The structural morphism `V → U_n` of an object `V/U_n` of `(LC_qc/U)_total`, in `LC_qc`. -/
def structureMap (Z : qcTotal.{x} S U a) : Z.left.left ⟶ U.obj Z.right :=
  (structureHom Z).left

/-- The structural morphism of an object of `(LC_qc/U)_total`, followed by the augmentation, is
the structure morphism to `X`. -/
@[reassoc (attr := simp)]
theorem structureMap_comp_app (Z : qcTotal.{x} S U a) :
    structureMap Z ≫ a.app Z.right = Z.left.hom :=
  Over.w (structureHom Z)

/-- A morphism of `(LC_qc/U)_total` from a morphism of the underlying objects and a simplicial
structure map forming a commutative square with the structural morphisms. -/
def qcTotalHomMk {Z Z' : qcTotal.{x} S U a} (g : Z.left ⟶ Z'.left) (φ : Z.right ⟶ Z'.right)
    (h : g.left ≫ structureMap Z' = structureMap Z ≫ U.map φ) : Z ⟶ Z' where
  left := g
  right := φ
  w := by
    rw [← incl_map_structureHom Z, ← incl_map_structureHom Z']
    dsimp only [Functor.comp_map]
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    exact Over.OverMorphism.ext h

/-- A morphism of `(LC_qc/U)_total` is a commutative square over a simplicial structure map. -/
theorem structureMap_naturality {Z Z' : qcTotal.{x} S U a} (f : Z ⟶ Z') :
    f.left.left ≫ structureMap Z' = structureMap Z ≫ U.map f.right := by
  have h : f.left ≫ structureHom Z' = structureHom Z ≫ (Over.lift U a).map f.right := by
    apply (FormalCoproduct.fullyFaithfulIncl (C := Over X)).map_injective
    simp only [Functor.map_comp]
    exact f.w
  exact congrArg CommaMorphism.left h

/-- The structural morphism of `V/U_n` is the open immersion `V → U_n`. -/
theorem structureMap_siteFunctorObj (P : SimplicialOpen (simplicialSpace S U)) :
    structureMap (siteFunctorObj.{x} S U a P) = (simplicialOpenSlice S U P).hom := by
  have h : structureHom (siteFunctorObj.{x} S U a P) =
      Over.homMk (simplicialOpenSlice S U P).hom := by
    apply (FormalCoproduct.fullyFaithfulIncl (C := Over X)).map_injective
    rw [incl_map_structureHom]
  exact congrArg CommaMorphism.left h

/-- The map of open subspaces underlying a morphism `Z → V/U_n`. -/
def toSiteFunctorLeft {Z : qcTotal.{x} S U a} {P : SimplicialOpen (simplicialSpace S U)}
    (f : Z ⟶ (siteFunctor.{x} S U a).obj P) : Z.left.left ⟶ (simplicialOpenSlice S U P).left :=
  f.left.left

/-- For a morphism `f : Z → V/U_n`, the map `toSiteFunctorLeft f` followed by the open immersion
`V → U_n` is the structural morphism of `Z` followed by the simplicial structure map of `f`. -/
@[reassoc]
theorem toSiteFunctorLeft_comp {Z : qcTotal.{x} S U a} {P : SimplicialOpen (simplicialSpace S U)}
    (f : Z ⟶ (siteFunctor.{x} S U a).obj P) :
    toSiteFunctorLeft f ≫ (simplicialOpenSlice S U P).hom = structureMap Z ≫ U.map f.right := by
  rw [← structureMap_siteFunctorObj]
  exact structureMap_naturality f

/-- A morphism `Z → V/U_n` lands, after the structural morphism of `Z` and the simplicial
structure map, in the open `V`. -/
theorem mem_of_hom_siteFunctor {Z : qcTotal.{x} S U a} {P : SimplicialOpen (simplicialSpace S U)}
    (f : Z ⟶ (siteFunctor.{x} S U a).obj P) (z : Z.left.left.obj) :
    (structureMap Z ≫ U.map f.right) z ∈ P.toOpens := by
  rw [← toSiteFunctorLeft_comp f]
  exact mem_of_factors (U.obj P.degree) P.toOpens _ z

/-- A morphism into `V/U_n` is determined by its simplicial structure map. -/
theorem siteFunctor_hom_ext {Z : qcTotal.{x} S U a} {P : SimplicialOpen (simplicialSpace S U)}
    {f g : Z ⟶ (siteFunctor.{x} S U a).obj P} (h : f.right = g.right) : f = g := by
  apply Comma.hom_ext
  · apply Over.OverMorphism.ext
    exact opensToSlice_hom_ext (U.obj P.degree) P.toOpens
      (f := toSiteFunctorLeft f) (g := toSiteFunctorLeft g)
      (by rw [toSiteFunctorLeft_comp, toSiteFunctorLeft_comp, h])
  · exact h

/-- The morphism `Z → V/U_n` with a prescribed simplicial structure map `φ`, when the structural
morphism of `Z` followed by `U(φ)` lands in `V`. -/
def toSiteFunctor (Z : qcTotal.{x} S U a) (P : SimplicialOpen (simplicialSpace S U))
    (φ : Z.right ⟶ P.degree) (h : ∀ z, (structureMap Z ≫ U.map φ) z ∈ P.toOpens) :
    Z ⟶ (siteFunctor.{x} S U a).obj P :=
  qcTotalHomMk
    (Over.homMk (opensFactor (U.obj P.degree) P.toOpens _ h) (by
      change opensFactor _ _ _ h ≫ ((simplicialOpenSlice S U P).hom ≫ a.app P.degree) = _
      rw [opensFactor_comp_assoc, Category.assoc, augmentation_naturality,
        structureMap_comp_app]))
    φ (by
      change opensFactor _ _ _ h ≫ structureMap (siteFunctorObj.{x} S U a P) = _
      rw [structureMap_siteFunctorObj, opensFactor_comp]
      rfl)

/-- The simplicial structure map of `toSiteFunctor Z P φ h` is `φ`. -/
@[simp]
theorem toSiteFunctor_right (Z : qcTotal.{x} S U a) (P : SimplicialOpen (simplicialSpace S U))
    (φ : Z.right ⟶ P.degree) (h : ∀ z, (structureMap Z ≫ U.map φ) z ∈ P.toOpens) :
    (toSiteFunctor Z P φ h).right = φ := rfl

/-- The simplicial structure map of the image of a morphism `f` of simplicial opens under
`V ↦ V/U_n` is the simplicial structure map of `f`. -/
@[simp]
theorem siteFunctor_map_right {P Q : SimplicialOpen (simplicialSpace S U)} (f : P ⟶ Q) :
    ((siteFunctor.{x} S U a).map f).right = f.base := rfl

variable (S U a)

/-- The functor `U_Zar → (LC_qc/U)_total`, `V ↦ V/U_n`, is representably flat: the simplicial
opens through which a given object of the total site maps form a cofiltered category. -/
instance siteFunctor_representablyFlat : RepresentablyFlat (siteFunctor.{x} S U a) := by
  constructor
  intro Z
  refine { cone_objs := ?_, cone_maps := ?_, nonempty := ?_ }
  · intro A B
    let C : SimplicialOpen (simplicialSpace S U) :=
      ⟨Z.right, (Opens.map ((simplicialSpace S U).map A.hom.right)).obj A.right.toOpens ⊓
        (Opens.map ((simplicialSpace S U).map B.hom.right)).obj B.right.toOpens⟩
    let c : Z ⟶ (siteFunctor.{x} S U a).obj C := toSiteFunctor Z C (𝟙 _) (fun z => by
      rw [CategoryTheory.Functor.map_id, Category.comp_id]
      exact ⟨mem_of_hom_siteFunctor A.hom z, mem_of_hom_siteFunctor B.hom z⟩)
    refine ⟨StructuredArrow.mk c,
      StructuredArrow.homMk ⟨A.hom.right, inf_le_left⟩ (siteFunctor_hom_ext ?_),
      StructuredArrow.homMk ⟨B.hom.right, inf_le_right⟩ (siteFunctor_hom_ext ?_), trivial⟩
    · exact Category.id_comp _
    · exact Category.id_comp _
  · intro A B f g
    let C : SimplicialOpen (simplicialSpace S U) :=
      ⟨Z.right, (Opens.map ((simplicialSpace S U).map A.hom.right)).obj A.right.toOpens⟩
    let c : Z ⟶ (siteFunctor.{x} S U a).obj C := toSiteFunctor Z C (𝟙 _) (fun z => by
      rw [CategoryTheory.Functor.map_id, Category.comp_id]
      exact mem_of_hom_siteFunctor A.hom z)
    let k : StructuredArrow.mk c ⟶ A :=
      StructuredArrow.homMk ⟨A.hom.right, le_rfl⟩ (siteFunctor_hom_ext (Category.id_comp _))
    refine ⟨StructuredArrow.mk c, k, ?_⟩
    apply StructuredArrow.hom_ext
    apply SimplicialOpen.Hom.ext
    have hf := congrArg CommaMorphism.right (StructuredArrow.w f)
    have hg := congrArg CommaMorphism.right (StructuredArrow.w g)
    change A.hom.right ≫ f.right.base = B.hom.right at hf
    change A.hom.right ≫ g.right.base = B.hom.right at hg
    change A.hom.right ≫ f.right.base = A.hom.right ≫ g.right.base
    rw [hf, hg]
  · let C : SimplicialOpen (simplicialSpace S U) := ⟨Z.right, ⊤⟩
    exact ⟨StructuredArrow.mk (toSiteFunctor Z C (𝟙 _) (fun _ => trivial))⟩

variable {S U a} in
/-- The structural morphism of an object of `(LC_qc/U)_total` restricted along a morphism of
`LC_qc/X` into its underlying object. -/
theorem structureMap_verticalObject (Z : qcTotal.{x} S U a) {W : Over X} (g : W ⟶ Z.left) :
    structureMap (verticalObject Z g) = g.left ≫ structureMap Z :=
  rfl

/-- The functor `U_Zar → (LC_qc/U)_total`, `V ↦ V/U_n`, is cover-preserving. -/
theorem siteFunctor_coverPreserving :
    CoverPreserving (SimplicialOpen.grothendieckTopology (simplicialSpace S U))
      (qcTotalTopology.{x} S U a) (siteFunctor.{x} S U a) := by
  classical
  constructor
  intro P R hR
  obtain ⟨R₀, ⟨hlev, hcov⟩, hle⟩ := (SimplicialOpen.mem_grothendieckTopology _ P R).1 hR
  let B : S.category := (simplicialOpenSlice S U P).left
  let ι := {p : Σ Q : SimplicialOpen (simplicialSpace S U), Q ⟶ P // R₀ p.2}
  let T : Presieve B := Presieve.ofArrows (fun i : ι => (simplicialOpenSlice S U i.1.1).left)
    (fun i => siteFunctorMapLeft S U i.1.2)
  have hiso : ∀ i : ι, IsIso (U.map i.1.2.base) := fun i => by
    obtain ⟨e, he⟩ := hlev _ _ i.2
    rw [he]
    infer_instance
  have hT : T ∈ S.zariskiPrecoverage B := by
    show T ∈ (TopCat.precoverage.comap (toTop S)) B
    rw [Precoverage.mem_comap_iff]
    simp only [T, Presieve.map_ofArrows]
    show _ ∧ _
    constructor
    · rw [Presieve.ofArrows_mem_comap_jointlySurjectivePrecoverage_iff]
      intro y
      have hy : (simplicialOpenSlice S U P).hom y ∈ P.toOpens :=
        mem_of_factors (U.obj P.degree) P.toOpens (𝟙 _) y
      obtain ⟨Q, f, hf, y', hy', hfy⟩ := hcov _ hy
      refine ⟨⟨⟨Q, f⟩, hf⟩, ?_⟩
      obtain ⟨w, hw⟩ : y' ∈ Set.range ((simplicialOpenSlice S U Q).hom : _ → _) := by
        rw [((S.opensToSlice (U.obj Q.degree)).2 Q.toOpens).2]
        exact hy'
      refine ⟨w, ?_⟩
      apply ((S.opensToSlice (U.obj P.degree)).2 P.toOpens).1.injective
      have hc := ConcreteCategory.congr_hom (siteFunctorMapLeft_comp S U f) w
      exact hc.trans ((congrArg _ hw).trans hfy)
    · rw [MorphismProperty.ofArrows_mem_precoverage]
      intro i
      have := hiso i
      have hwhole := ((S.opensToSlice (U.obj P.degree)).2 P.toOpens).1
      have hinto : Topology.IsOpenEmbedding
          (((simplicialOpenSlice S U i.1.1).hom ≫ U.map i.1.2.base : _ ⟶ _) : _ → _) :=
        (TopCat.homeoOfIso (asIso ((toTop S).map (U.map i.1.2.base)))).isOpenEmbedding.comp
          ((S.opensToSlice (U.obj i.1.1.degree)).2 i.1.1.toOpens).1
      rw [← siteFunctorMapLeft_comp S U i.1.2] at hinto
      exact Topology.IsOpenEmbedding.of_comp _ hwhole hinto
  show verticalSieve _ ∈ (S.qcSite.grothendieckTopology.over X)
    ((siteFunctor.{x} S U a).obj P).left
  rw [GrothendieckTopology.mem_over_iff]
  apply S.zariskiTopology_le_qc
  refine S.zariskiTopology.superset_covering ?_
    (S.zariskiPrecoverage.generate_mem_toGrothendieck hT)
  apply (Sieve.generate_le_iff _ _).2
  rintro W g ⟨i⟩
  refine (Sieve.overEquiv_iff (Y := ((siteFunctor.{x} S U a).obj P).left) _
    (siteFunctorMapLeft S U i.1.2)).2 ?_
  obtain ⟨⟨⟨d, VQ⟩, f⟩, hf⟩ := i
  obtain ⟨e, he⟩ := hlev _ f hf
  dsimp only at e
  subst e
  let Q : SimplicialOpen (simplicialSpace S U) := ⟨P.degree, VQ⟩
  have hbase : f.base = 𝟙 _ := he
  let g' : Over.mk (siteFunctorMapLeft S U f ≫ ((siteFunctor.{x} S U a).obj P).left.hom) ⟶
      ((siteFunctor.{x} S U a).obj Q).left :=
    Over.homMk (𝟙 _) (by
      show 𝟙 _ ≫ (simplicialOpenSlice S U Q).hom ≫ a.app P.degree =
        siteFunctorMapLeft S U f ≫ (simplicialOpenSlice S U P).hom ≫ a.app P.degree
      rw [siteFunctorMapLeft_comp_assoc, hbase, CategoryTheory.Functor.map_id,
        Category.id_comp, Category.id_comp])
  let gP : Over.mk (siteFunctorMapLeft S U f ≫ ((siteFunctor.{x} S U a).obj P).left.hom) ⟶
      ((siteFunctor.{x} S U a).obj P).left := Over.homMk (siteFunctorMapLeft S U f)
  let k : verticalObject ((siteFunctor.{x} S U a).obj P) gP ⟶ (siteFunctor.{x} S U a).obj Q :=
    qcTotalHomMk g' (𝟙 _) (by
      rw [structureMap_verticalObject]
      show 𝟙 _ ≫ structureMap (siteFunctorObj.{x} S U a Q) =
        siteFunctorMapLeft S U f ≫ structureMap (siteFunctorObj.{x} S U a P) ≫ U.map (𝟙 _)
      rw [structureMap_siteFunctorObj, structureMap_siteFunctorObj,
        CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp,
        siteFunctorMapLeft_comp, hbase, CategoryTheory.Functor.map_id, Category.comp_id])
  refine ⟨Q, f, k, hle _ f hf, ?_⟩
  apply Comma.hom_ext
  · apply Over.OverMorphism.ext
    exact (Category.id_comp _).symm
  · show 𝟙 _ = 𝟙 _ ≫ f.base
    rw [hbase, Category.id_comp]

/-- The functor `U_Zar → (LC_qc/U)_total`, `V ↦ V/U_n`, is continuous. -/
instance siteFunctor_isContinuous :
    (siteFunctor.{x} S U a).IsContinuous (SimplicialOpen.grothendieckTopology (simplicialSpace S U))
      (qcTotalTopology.{x} S U a) :=
  Functor.isContinuous_iff_coverPreserving.2 (siteFunctor_coverPreserving.{x} S U a)

/-- For an object `Z` of `(LC_qc/U)_total`, the category of costructured arrows from
`(V ↦ V/U_n)ᵒᵖ` to `Z` is `u`-small. -/
instance small_costructuredArrow_siteFunctor (Z : (qcTotal.{x} S U a)ᵒᵖ) :
    Small.{u} (CostructuredArrow (siteFunctor.{x} S U a).op Z) :=
  small_self _

/-- Restriction of sheaves of sets along the continuous functor `V ↦ V/U_n` is a right adjoint. -/
instance siteFunctor_sheafPushforwardContinuous_isRightAdjoint :
    ((siteFunctor.{x} S U a).sheafPushforwardContinuous (Type u)
      (SimplicialOpen.grothendieckTopology (simplicialSpace S U))
      (qcTotalTopology.{x} S U a)).IsRightAdjoint := by
  have := hasSheafify_qcTotalTopology.{x} S U a
  infer_instance

/-- The inverse image of sheaves of sets along the continuous functor `V ↦ V/U_n` is left
exact. -/
theorem siteFunctor_sheafPullback_preservesFiniteLimits :
    PreservesFiniteLimits ((siteFunctor.{x} S U a).sheafPullback (Type u)
      (SimplicialOpen.grothendieckTopology (simplicialSpace S U))
      (qcTotalTopology.{x} S U a)) := by
  let G := siteFunctor.{x} S U a
  have := hasSheafify_qcTotalTopology.{x} S U a
  have : PreservesFiniteLimits
      (G.op.lan : ((SimplicialOpen (simplicialSpace S U))ᵒᵖ ⥤ Type u) ⥤
        ((qcTotal.{x} S U a)ᵒᵖ ⥤ Type u)) :=
    lan_preservesFiniteLimits_of_flat (F := G) (hPres := fun _ => inferInstance)
  exact Functor.sheafPullbackConstruction.preservesFiniteLimits _ _ _ _

/-- The morphism of topoi `h : Sh((LC_qc/U)_total) → Sh(U_Zar)` of the continuous functor
`U_Zar → (LC_qc/U)_total`, `V ↦ V/U_n`: its direct image is restriction along that functor, its
inverse image the sheaf pullback. -/
def totalComparisonMorphism :
    MorphismOfTopoi (Sheaf (qcTotalTopology.{x} S U a) (Type u))
      (Sheaf (SimplicialOpen.grothendieckTopology (simplicialSpace S U)) (Type u)) where
  pushforward := (siteFunctor.{x} S U a).sheafPushforwardContinuous (Type u) _ _
  inverseImage := (siteFunctor.{x} S U a).sheafPullback (Type u) _ _
  adj := (siteFunctor.{x} S U a).sheafAdjunctionContinuous (Type u) _ _
  preservesFiniteLimits := siteFunctor_sheafPullback_preservesFiniteLimits.{x} S U a

end Stacks.Topology.LocallyQuasiCompactZariskiSituation

end
