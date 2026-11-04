module

public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.LocallyInjective
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomComplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Slice.RestrictionOfComplexes
public import StacksFrontier.CategoryTheory.Sites.Modules.Flat
public import StacksFrontier.Algebra.Homology.DerivedCategory.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Derived internal Hom after localization

For a flat epimorphism of sheaves of commutative rings, derived internal Hom between complexes
of modules over the target can be computed over either ring. In particular this applies to
localization at a global section.

## Main results

* `AlgebraicGeometry.RingedSite.restrictScalars_fullyFaithful_of_epi` is [Stacks, Tag 0930] for
  commutative coefficients: restriction of scalars along an epimorphism of sheaves of
  commutative rings is fully faithful.
* `AlgebraicGeometry.RingedSite.derivedSheafHom_restrictScalarsIso` compares the two derived
  internal Hom complexes after restriction of scalars.
* `AlgebraicGeometry.RingedSite.derivedSheafHom_restrictScalarsIso_canonical` characterizes the
  comparison as the identity on the local Hom complexes.
* `AlgebraicGeometry.RingedSite.sheafHomComplex_localizedAction_agree` identifies the actions of
  a localized section on the source and target of each local Hom.

## Implementation notes

The statement uses a K-injective representative for the second derived argument. This computes
derived internal Hom for every pair of objects in the unbounded derived category. The comparison
is formulated over the original structure sheaf; the right-hand side retains the localized module
structure. The canonical characterization specifies a complex-level isomorphism inducing the
derived comparison and acting identically on every local Hom component. The action-agreement
result expresses equality of the two localized actions pointwise on these components.
Flat epimorphy is the property of localization used by the proof: it makes restriction of scalars
fully faithful, because a local section of the target ring sheaf satisfies `r ⊗ 1 = 1 ⊗ r`
locally, which is exactly the statement that an additive map of the restrictions is already
linear over the target.

## References

* [Stacks Project, Tag 0930](https://stacks.math.columbia.edu/tag/0930)
* [Stacks Project, Tag 0996](https://stacks.math.columbia.edu/tag/0996)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSite

section Tensor

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  {O S : Sheaf J CommRingCat.{u}} (f : O ⟶ S)

/-- The presheaf `U ↦ S(U) ⊗_{O(U)} S(U)`, used to express locally the relation `r ⊗ 1 = 1 ⊗ r`
satisfied by a section of an epimorphic extension. -/
private noncomputable def tensorPresheaf : Cᵒᵖ ⥤ CommRingCat.{u} := by
  let (U : Cᵒᵖ) : Algebra (O.obj.obj U) (S.obj.obj U) := (f.hom.app U).hom.toAlgebra
  exact {
    obj U := CommRingCat.of (S.obj.obj U ⊗[O.obj.obj U] S.obj.obj U)
    map {U V} g := CommRingCat.ofHom (Algebra.TensorProduct.mapRingHom
      (O.obj.map g).hom (S.obj.map g).hom (S.obj.map g).hom
      (congrArg CommRingCat.Hom.hom (f.hom.naturality g).symm)
      (congrArg CommRingCat.Hom.hom (f.hom.naturality g).symm))
    map_id U := by
      apply CommRingCat.hom_ext
      apply Algebra.TensorProduct.ringHom_ext <;> ext x <;> simp
    map_comp g h := by
      apply CommRingCat.hom_ext
      apply Algebra.TensorProduct.ringHom_ext <;> ext x <;> simp }

/-- Inclusion of `S` into the first factor of `tensorPresheaf f`. -/
private noncomputable def tensorLeft : S.obj ⟶ tensorPresheaf f where
  app U := by
    let := (f.hom.app U).hom.toAlgebra
    exact CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom
  naturality {U V} g := by
    ext x
    simp [tensorPresheaf]

/-- Inclusion of `S` into the second factor of `tensorPresheaf f`. -/
private noncomputable def tensorRight : S.obj ⟶ tensorPresheaf f where
  app U := by
    let := (f.hom.app U).hom.toAlgebra
    exact CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom
  naturality {U V} g := by
    ext x
    simp [tensorPresheaf]

/-- For an epimorphism the two inclusions agree after sheafification. -/
private theorem tensorLeft_right [Epi f] :
    tensorLeft f ≫ toSheafify J (tensorPresheaf f) =
      tensorRight f ≫ toSheafify J (tensorPresheaf f) := by
  let a : S ⟶ (presheafToSheaf J CommRingCat).obj (tensorPresheaf f) :=
    ⟨tensorLeft f ≫ toSheafify J (tensorPresheaf f)⟩
  let b : S ⟶ (presheafToSheaf J CommRingCat).obj (tensorPresheaf f) :=
    ⟨tensorRight f ≫ toSheafify J (tensorPresheaf f)⟩
  have h : f ≫ a = f ≫ b := by
    apply ObjectProperty.hom_ext
    show f.hom ≫ (tensorLeft f ≫ _) = f.hom ≫ (tensorRight f ≫ _)
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    ext U r
    let := (f.hom.app U).hom.toAlgebra
    exact (Algebra.TensorProduct.algebraMap_apply (S := O.obj.obj U) r).symm.trans
      (Algebra.TensorProduct.algebraMap_apply' r)
  exact congrArg (fun k ↦ k.hom) ((cancel_epi f).1 h)

/-- Every local section of `S` satisfies `r ⊗ 1 = 1 ⊗ r` on a covering sieve. -/
private theorem tensor_relation_cover [Epi f] (U : Cᵒᵖ) (s : S.obj.obj U) :
    Presheaf.equalizerSieve
      ((tensorLeft f).app U s)
      ((tensorRight f).app U s) ∈ J U.unop := by
  apply Presheaf.equalizerSieve_mem J (toSheafify J (tensorPresheaf f))
  exact ConcreteCategory.congr_hom (NatTrans.congr_app (tensorLeft_right f) U) s

/-- An additive map between `B`-modules that commutes with the scalars from `A` commutes with a
scalar `b : B` satisfying `b ⊗ 1 = 1 ⊗ b`. -/
private theorem linear_smul_of_tmul_eq
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {M N : Type u} [AddCommGroup M] [AddCommGroup N] [Module B M] [Module B N]
    (h : M →+ N) (hA : ∀ (a : A) (x : M), h (algebraMap A B a • x) = algebraMap A B a • h x)
    (b : B) (hb : b ⊗ₜ[A] 1 = 1 ⊗ₜ[A] b) (x : M) :
    h (b • x) = b • h x := by
  let : Module A M := Module.compHom M (algebraMap A B)
  let : Module A N := Module.compHom N (algebraMap A B)
  have : IsScalarTower A B M := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have : IsScalarTower A B N := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let k : B →ₗ[A] B →ₗ[A] N :=
    { toFun := fun s ↦ s • (({ h with map_smul' := hA } : M →ₗ[A] N).comp
        ((LinearMap.toSpanSingleton B M x).restrictScalars A))
      map_add' := by
        intros
        ext
        simp [add_smul]
      map_smul' := by
        intros
        ext
        simp [smul_assoc] }
  simpa [k] using (congrArg (TensorProduct.lift k) hb).symm

/-- A morphism of restrictions of scalars along an epimorphism is already linear over the
target. -/
private theorem restrictScalars_linear [Epi f]
    (M N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S))
    (g : (SheafOfModules.restrictScalars (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
        (R' := Stacks.SheafOfModules.Tensor.ringSheaf S)
        (ObjectProperty.homMk (Functor.whiskerRight f.hom (forget₂ CommRingCat RingCat)))).obj M ⟶
      (SheafOfModules.restrictScalars (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
        (R' := Stacks.SheafOfModules.Tensor.ringSheaf S)
        (ObjectProperty.homMk (Functor.whiskerRight f.hom (forget₂ CommRingCat RingCat)))).obj N)
    (U : Cᵒᵖ) (r : S.obj.obj U) (x : M.val.obj U) :
    g.val.app U ((M.val.obj U).isModule.smul r x) =
      (N.val.obj U).isModule.smul r (g.val.app U x) := by
  let (V : Cᵒᵖ) : Module (S.obj.obj V) (M.val.obj V) := (M.val.obj V).isModule
  let (V : Cᵒᵖ) : Module (S.obj.obj V) (N.val.obj V) := (N.val.obj V).isModule
  let T := Presheaf.equalizerSieve ((tensorLeft f).app U r) ((tensorRight f).app U r)
  have hsep : Presieve.IsSeparated J (N.val.presheaf ⋙ forget AddCommGrpCat) := by
    apply Presieve.IsSheaf.isSeparated
    rw [← isSheaf_iff_isSheaf_of_type]
    exact ((sheafCompose J (forget AddCommGrpCat)).obj
      ((SheafOfModules.toSheaf _).obj N)).property
  apply (hsep T (tensor_relation_cover f U r)).ext
  intro V k hk
  show N.val.map k.op (g.val.app U (r • x)) =
    N.val.map k.op (r • (show N.val.obj U from g.val.app U x))
  have hn : ∀ y : M.val.obj U,
      N.val.map k.op (g.val.app U y) = g.val.app (op V) (M.val.map k.op y) :=
    fun y ↦ (PresheafOfModules.naturality_apply g.val k.op y).symm
  let := (f.hom.app (op V)).hom.toAlgebra
  have ht : S.obj.map k.op r ⊗ₜ[O.obj.obj (op V)] (1 : S.obj.obj (op V)) =
      (1 : S.obj.obj (op V)) ⊗ₜ[O.obj.obj (op V)] S.obj.map k.op r := by
    change (tensorPresheaf f).map k.op ((tensorLeft f).app U r) =
      (tensorPresheaf f).map k.op ((tensorRight f).app U r) at hk
    exact (ConcreteCategory.congr_hom ((tensorLeft f).naturality k.op) r).trans
      (hk.trans (ConcreteCategory.congr_hom ((tensorRight f).naturality k.op) r).symm)
  have hl := linear_smul_of_tmul_eq (A := O.obj.obj (op V)) (B := S.obj.obj (op V))
    (M := M.val.obj (op V)) (N := N.val.obj (op V)) (g.val.app (op V)).hom.toAddMonoidHom
    (fun a y ↦ (g.val.app (op V)).hom.map_smul a y) (S.obj.map k.op r) ht (M.val.map k.op x)
  refine (hn (r • x)).trans ?_
  refine (congrArg (fun z ↦ (g.val.app (op V)) z) (M.val.map_smul k.op r x)).trans ?_
  refine hl.trans ?_
  refine (congrArg (fun z : N.val.obj (op V) ↦ S.obj.map k.op r • z) (hn x).symm).trans ?_
  exact (N.val.map_smul k.op r (show N.val.obj U from g.val.app U x)).symm

/-- Restriction of scalars along an epimorphism of sheaves of commutative rings is fully
faithful. -/
private noncomputable def restrictScalars_fullyFaithful [Epi f] :
    (SheafOfModules.restrictScalars.{u} (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
      (R' := Stacks.SheafOfModules.Tensor.ringSheaf S)
      (ObjectProperty.homMk
        (Functor.whiskerRight f.hom (forget₂ CommRingCat RingCat)))).FullyFaithful where
  preimage {M N} g := ⟨{
    app U := ModuleCat.ofHom
      { __ := (g.val.app U).hom.toAddMonoidHom
        map_smul' r x := restrictScalars_linear f M N g U r x }
    naturality {U V} k := by
      ext x
      exact PresheafOfModules.naturality_apply g.val k x }⟩
  map_preimage g := by ext; rfl
  preimage_map g := by ext; rfl

/-- **Stacks Tag 0930 for commutative coefficients.** Restriction of scalars along an
epimorphism `f : 𝒪 ⟶ 𝒪'` of sheaves of *commutative* rings on a site is fully faithful.

Unlike `Stacks.NoncommChangeOfRings.Silver.restrictScalars_fullyFaithful_of_epi`, which proves
the same for sheaves of not necessarily commutative rings, the epimorphism is asked for in the
category of sheaves of commutative rings — which is the category [Stacks, Tag 0996] localizes in
— and no smallness hypothesis on the site is needed. The argument is that a local section `r` of
`𝒪'` satisfies `r ⊗ 1 = 1 ⊗ r` locally, which says exactly that an additive map of the
restrictions is already `𝒪'`-linear. -/
theorem restrictScalars_fullyFaithful_of_epi [Epi f] :
    Nonempty (SheafOfModules.restrictScalars.{u} (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
      (R' := Stacks.SheafOfModules.Tensor.ringSheaf S)
      (ObjectProperty.homMk
        (Functor.whiskerRight f.hom (forget₂ CommRingCat RingCat)))).FullyFaithful :=
  ⟨restrictScalars_fullyFaithful f⟩

/-- Restriction of scalars on a slice site is fully faithful, since the pullback of an
epimorphism to the slice is again an epimorphism. -/
private noncomputable def restrictScalars_over_fullyFaithful [Epi f] (U : C) :
    (SheafOfModules.restrictScalars.{u} (R := (Stacks.SheafOfModules.Tensor.ringSheaf O).over U)
      (R' := (Stacks.SheafOfModules.Tensor.ringSheaf S).over U)
      ((J.overPullback RingCat U).map
        (ObjectProperty.homMk
          (Functor.whiskerRight f.hom (forget₂ CommRingCat RingCat))))).FullyFaithful := by
  let F := J.overPullback CommRingCat.{u} U
  have : F.PreservesEpimorphisms := Functor.preservesEpimorphisms_of_adjunction
    ((Over.forget U).sheafAdjunctionCocontinuous CommRingCat.{u} (J.over U) J)
  have : Epi (F.map f) := Functor.map_epi F f
  exact restrictScalars_fullyFaithful (F.map f)

end Tensor

/-- A fully faithful additive functor induces an isomorphism of Hom complexes. -/
private noncomputable def homComplexMapIso
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    [Preadditive C] [Preadditive D] (Φ : C ⥤ D) [Φ.Additive]
    (hΦ : Φ.FullyFaithful) (K L : CochainComplex C ℤ) :
    CochainComplex.HomComplex K L ≅
      CochainComplex.HomComplex
        ((Φ.mapHomologicalComplex (.up ℤ)).obj K)
        ((Φ.mapHomologicalComplex (.up ℤ)).obj L) := by
  let cochainEquiv (n : ℤ) :
      CochainComplex.HomComplex.Cochain K L n ≃+
        CochainComplex.HomComplex.Cochain
          ((Φ.mapHomologicalComplex (.up ℤ)).obj K)
          ((Φ.mapHomologicalComplex (.up ℤ)).obj L) n :=
    { toFun := fun z ↦ z.map Φ
      invFun := fun z ↦ CochainComplex.HomComplex.Cochain.mk
        (fun p q hpq ↦ hΦ.preimage (z.v p q hpq))
      left_inv := fun z ↦ by
        ext p q hpq
        simp [CochainComplex.HomComplex.Cochain.map, hΦ.preimage_map]
      right_inv := fun z ↦ by
        ext p q hpq
        simp [CochainComplex.HomComplex.Cochain.map, hΦ.map_preimage]
      map_add' := fun z z' ↦ CochainComplex.HomComplex.Cochain.map_add z z' Φ }
  refine HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (cochainEquiv n).toAddCommGrpIso) fun n m _ ↦ ?_
  ext z
  change CochainComplex.HomComplex.δ n m (z.map Φ) =
    (CochainComplex.HomComplex.δ n m z).map Φ
  exact CochainComplex.HomComplex.δ_map n m z Φ

/-- The ringed site with the same underlying site and the localized structure sheaf. -/
private abbrev localizedSite (X : RingedSite.{u, u, u})
    (Oh : Sheaf X.J CommRingCat.{u}) : RingedSite.{u, u, u} :=
  { C := X.C, J := X.J, O := Oh }

/-- Restriction of scalars along the localization map. -/
private noncomputable abbrev restrictionFunctor (X : RingedSite.{u, u, u})
    (Oh : Sheaf X.J CommRingCat.{u}) (f : X.O ⟶ Oh) :=
  SheafOfModules.restrictScalars.{u} (R := Stacks.SheafOfModules.Tensor.ringSheaf X.O)
    (R' := Stacks.SheafOfModules.Tensor.ringSheaf Oh)
    (ObjectProperty.homMk (Functor.whiskerRight f.hom (forget₂ CommRingCat RingCat)))

/-- Restriction of scalars along the localization map, pulled back to a slice site. -/
private noncomputable abbrev sliceRestriction (X : RingedSite.{u, u, u})
    (Oh : Sheaf X.J CommRingCat.{u}) (f : X.O ⟶ Oh) (U : X.C) :=
  SheafOfModules.restrictScalars.{u} (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)
    (R' := (Stacks.SheafOfModules.Tensor.ringSheaf Oh).over U)
    ((X.J.overPullback RingCat U).map
      (ObjectProperty.homMk (Functor.whiskerRight f.hom (forget₂ CommRingCat RingCat))))

/-- The degreewise restriction of a complex of modules along the localization map. -/
private noncomputable abbrev restrictedComplex (X : RingedSite.{u, u, u})
    (Oh : Sheaf X.J CommRingCat.{u}) (f : X.O ⟶ Oh)
    (L : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf Oh)) ℤ) :=
  ((restrictionFunctor X Oh f).mapHomologicalComplex (.up ℤ)).obj L

section Comparison

variable (X : RingedSite.{u, u, u}) (Oh : Sheaf X.J CommRingCat.{u}) (f : X.O ⟶ Oh)
  (L I : CochainComplex (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf Oh)) ℤ)

/-- The comparison of section complexes on a slice site: a cochain over the localized ring is
sent to the same cochain viewed over the original ring. -/
private noncomputable def sectionComparison (U : X.C) :
    sectionComplex (localizedSite X Oh) (sheafHomComplex (localizedSite X Oh) L I).obj U ⟶
      sectionComplex X (sheafHomComplex X (restrictedComplex X Oh f L)
        (restrictedComplex X Oh f I)).obj U := by
  let F := sliceRestriction X Oh f U
  let K := restrictComplex (localizedSite X Oh) L U
  let Jc := restrictComplex (localizedSite X Oh) I U
  let m : K.HomComplex Jc ⟶
      CochainComplex.HomComplex ((F.mapHomologicalComplex (.up ℤ)).obj K)
        ((F.mapHomologicalComplex (.up ℤ)).obj Jc) := {
    f n := AddCommGrpCat.ofHom
      { toFun := fun z ↦ z.map F
        map_zero' := CochainComplex.HomComplex.Cochain.map_zero K Jc n F
        map_add' := fun z z' ↦ CochainComplex.HomComplex.Cochain.map_add z z' F }
    comm' n m h := by
      ext z
      exact CochainComplex.HomComplex.δ_map n m z F }
  exact ((sheafHomComplex (localizedSite X Oh) L I).sectionsIso U).hom ≫ m ≫
    ((sheafHomComplex X (restrictedComplex X Oh f L)
      (restrictedComplex X Oh f I)).sectionsIso U).inv

/-- The section comparison leaves every local module homomorphism unchanged. -/
private theorem sectionComparison_apply (U : X.C) (n p q : ℤ) (hpq : p + n = q)
    (s : ((sheafHomComplex (localizedSite X Oh) L I).obj.X n).val.obj (op U))
    {W : X.C} (g : W ⟶ U) (x : (L.X p).val.obj (op W)) :
    (((AddCommGrpCat.Hom.hom (((sheafHomComplex X (restrictedComplex X Oh f L)
        (restrictedComplex X Oh f I)).sectionsIso U).hom.f n)
        ((sectionComparison X Oh f L I U).f n s)).v p q hpq).val.app
        (op (Over.mk g))) x =
      (((AddCommGrpCat.Hom.hom
        (((sheafHomComplex (localizedSite X Oh) L I).sectionsIso U).hom.f n) s).v
          p q hpq).val.app (op (Over.mk g))) x := by
  have he := ConcreteCategory.congr_hom
    (HomologicalComplex.congr_hom ((sheafHomComplex X (restrictedComplex X Oh f L)
      (restrictedComplex X Oh f I)).sectionsIso U).inv_hom_id n)
    ((AddCommGrpCat.Hom.hom
      (((sheafHomComplex (localizedSite X Oh) L I).sectionsIso U).hom.f n) s).map
        (sliceRestriction X Oh f U))
  change (((sheafHomComplex X (restrictedComplex X Oh f L)
        (restrictedComplex X Oh f I)).sectionsIso U).hom.f n).hom
      ((((sheafHomComplex X (restrictedComplex X Oh f L)
        (restrictedComplex X Oh f I)).sectionsIso U).inv.f n).hom
        ((AddCommGrpCat.Hom.hom
          (((sheafHomComplex (localizedSite X Oh) L I).sectionsIso U).hom.f n) s).map
            (sliceRestriction X Oh f U))) =
      (AddCommGrpCat.Hom.hom
        (((sheafHomComplex (localizedSite X Oh) L I).sectionsIso U).hom.f n) s).map
          (sliceRestriction X Oh f U) at he
  exact congrArg (fun z ↦ ((z.v p q hpq).val.app (op (Over.mk g))) x) he

/-- Sections of the internal Hom complex are determined by their values on local module
homomorphisms. -/
private theorem sections_ext (U : X.C) (n : ℤ)
    (s t : ((sheafHomComplex X (restrictedComplex X Oh f L)
      (restrictedComplex X Oh f I)).obj.X n).val.obj (op U))
    (h : ∀ (p q : ℤ) (hpq : p + n = q) {W : X.C} (g : W ⟶ U)
      (x : (L.X p).val.obj (op W)),
      (((AddCommGrpCat.Hom.hom (((sheafHomComplex X (restrictedComplex X Oh f L)
        (restrictedComplex X Oh f I)).sectionsIso U).hom.f n) s).v p q hpq).val.app
        (op (Over.mk g))) x =
      (((AddCommGrpCat.Hom.hom (((sheafHomComplex X (restrictedComplex X Oh f L)
        (restrictedComplex X Oh f I)).sectionsIso U).hom.f n) t).v p q hpq).val.app
        (op (Over.mk g))) x) : s = t := by
  apply (ConcreteCategory.bijective_of_isIso
    (((sheafHomComplex X (restrictedComplex X Oh f L)
      (restrictedComplex X Oh f I)).sectionsIso U).hom.f n)).1
  apply CochainComplex.HomComplex.Cochain.ext
  intro p q hpq
  ext V x
  exact h p q hpq V.unop.hom x

/-- The section comparison is linear over the original structure sheaf. -/
private theorem sectionComparison_smul (U : X.Cᵒᵖ) (n : ℤ)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U)
    (s : ((sheafHomComplex (localizedSite X Oh) L I).obj.X n).val.obj U) :
    (sectionComparison X Oh f L I U.unop).f n
      ((((restrictionFunctor X Oh f).obj
        ((sheafHomComplex (localizedSite X Oh) L I).obj.X n)).val.obj U).isModule.smul r s) =
    (((sheafHomComplex X (restrictedComplex X Oh f L)
      (restrictedComplex X Oh f I)).obj.X n).val.obj U).isModule.smul r
      ((sectionComparison X Oh f L I U.unop).f n s) := by
  apply sections_ext X Oh f L I U.unop n
  intro p q hpq W g x
  have e₁ := sectionComparison_apply X Oh f L I U.unop n p q hpq
    ((((restrictionFunctor X Oh f).obj
      ((sheafHomComplex (localizedSite X Oh) L I).obj.X n)).val.obj U).isModule.smul r s) g x
  have e₂ := (sheafHomComplex (localizedSite X Oh) L I).smul_natural U.unop
    (f.hom.app U r) n p q hpq s g x
  have e₃ := (sheafHomComplex X (restrictedComplex X Oh f L)
    (restrictedComplex X Oh f I)).smul_natural U.unop r n p q hpq
    ((sectionComparison X Oh f L I U.unop).f n s) g x
  have e₄ := sectionComparison_apply X Oh f L I U.unop n p q hpq s g x
  have e := ConcreteCategory.congr_hom (f.hom.naturality g.op) r
  exact e₁.trans (e₂.trans ((congrArg₂
    (fun a t ↦ ((I.X q).val.obj (op W)).isModule.smul a t)
    e.symm e₄.symm).trans e₃.symm))

/-- The comparison map of internal Hom complexes. -/
private noncomputable def comparisonMap :
    ((restrictionFunctor X Oh f).mapHomologicalComplex (.up ℤ)).obj
        (sheafHomComplex (localizedSite X Oh) L I).obj ⟶
      (sheafHomComplex X (restrictedComplex X Oh f L)
        (restrictedComplex X Oh f I)).obj where
  f n := ⟨{
    app U := ModuleCat.ofHom
      (X := (((restrictionFunctor X Oh f).mapHomologicalComplex (.up ℤ)).obj
        (sheafHomComplex (localizedSite X Oh) L I).obj).X n |>.val.obj U)
      (Y := ((sheafHomComplex X (restrictedComplex X Oh f L)
        (restrictedComplex X Oh f I)).obj.X n).val.obj U)
      { toFun s := (sectionComparison X Oh f L I U.unop).f n s
        map_add' s t := ((sectionComparison X Oh f L I U.unop).f n).hom.map_add s t
        map_smul' r s := sectionComparison_smul X Oh f L I U n r s }
    naturality {U V} g := by
      ext s
      apply sections_ext X Oh f L I V.unop n
      intro p q hpq W k x
      have e₁ := sectionComparison_apply X Oh f L I V.unop n p q hpq
        (((sheafHomComplex (localizedSite X Oh) L I).obj.X n).val.map g s) k x
      have e₂ := (sheafHomComplex (localizedSite X Oh) L I).restrict_natural
        g.unop n p q hpq s k x
      have e₃ := sectionComparison_apply X Oh f L I U.unop n p q hpq s (k ≫ g.unop) x
      have e₄ := (sheafHomComplex X (restrictedComplex X Oh f L)
        (restrictedComplex X Oh f I)).restrict_natural g.unop n p q hpq
        ((sectionComparison X Oh f L I U.unop).f n s) k x
      exact e₁.trans (e₂.symm.trans (e₃.symm.trans e₄)) }⟩
  comm' n m h := by
    ext U s
    exact ConcreteCategory.congr_hom ((sectionComparison X Oh f L I U.unop).comm n m) s

/-- On every slice site the comparison is an isomorphism, because restriction of scalars there
is fully faithful. -/
private theorem sectionComparison_isIso [Epi f] (U : X.C) :
    IsIso (sectionComparison X Oh f L I U) := by
  let e := (sheafHomComplex (localizedSite X Oh) L I).sectionsIso U ≪≫
    homComplexMapIso (sliceRestriction X Oh f U)
      (restrictScalars_over_fullyFaithful f U)
      (restrictComplex (localizedSite X Oh) L U)
      (restrictComplex (localizedSite X Oh) I U) ≪≫
    ((sheafHomComplex X (restrictedComplex X Oh f L)
      (restrictedComplex X Oh f I)).sectionsIso U).symm
  exact inferInstanceAs (IsIso e.hom)

/-- The comparison map is an isomorphism. -/
private theorem comparisonMap_isIso [Epi f] : IsIso (comparisonMap X Oh f L I) := by
  have hn (n : ℤ) : IsIso ((comparisonMap X Oh f L I).f n) := by
    let F := SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
      sheafToPresheaf X.J AddCommGrpCat
    have hi : IsIso (F.map ((comparisonMap X Oh f L I).f n)) := by
      refine (NatTrans.isIso_iff_isIso_app _).2 fun U ↦ ?_
      have := sectionComparison_isIso X Oh f L I U.unop
      exact inferInstanceAs (IsIso ((sectionComparison X Oh f L I U.unop).f n))
    exact isIso_of_reflects_iso ((comparisonMap X Oh f L I).f n) F
  exact HomologicalComplex.Hom.isIso_of_components _

/-- The comparison isomorphism of internal Hom complexes. -/
private noncomputable def comparisonIso [Epi f] :
    (sheafHomComplex X (restrictedComplex X Oh f L) (restrictedComplex X Oh f I)).obj ≅
      ((restrictionFunctor X Oh f).mapHomologicalComplex (.up ℤ)).obj
        (sheafHomComplex (localizedSite X Oh) L I).obj :=
  have := comparisonMap_isIso X Oh f L I
  (asIso (comparisonMap X Oh f L I)).symm

/-- The comparison isomorphism leaves every local module homomorphism unchanged. -/
private theorem comparisonIso_apply [Epi f] (U : X.C) (n p q : ℤ) (hpq : p + n = q)
    (s : ((sheafHomComplex X (restrictedComplex X Oh f L)
      (restrictedComplex X Oh f I)).obj.X n).val.obj (op U))
    {W : X.C} (g : W ⟶ U) (x : (L.X p).val.obj (op W)) :
    (((AddCommGrpCat.Hom.hom
        (((sheafHomComplex (localizedSite X Oh) L I).sectionsIso U).hom.f n)
        (((comparisonIso X Oh f L I).hom.f n).val.app (op U) s)).v p q hpq).val.app
        (op (Over.mk g))) x =
      (((AddCommGrpCat.Hom.hom (((sheafHomComplex X (restrictedComplex X Oh f L)
        (restrictedComplex X Oh f I)).sectionsIso U).hom.f n) s).v p q hpq).val.app
        (op (Over.mk g))) x := by
  have hi := congrArg (fun k ↦ (k.f n).val.app (op U) s)
    (comparisonIso X Oh f L I).hom_inv_id
  change (sectionComparison X Oh f L I U).f n
    (((comparisonIso X Oh f L I).hom.f n).val.app (op U) s) = s at hi
  have := sectionComparison_apply X Oh f L I U n p q hpq
    (((comparisonIso X Oh f L I).hom.f n).val.app (op U) s) g x
  rw [hi] at this
  exact this.symm

end Comparison

/-- Derived internal Hom of modules over a flat epimorphic sheaf of rings is
unchanged after restricting scalars to the source.

This is the general helper, for an arbitrary `f : 𝒪 ⟶ 𝒪'` of sheaves of commutative rings that
is *assumed* to be an epimorphism and *assumed* flat. [Stacks, Tag 0996(1)] is the case
`f = (𝒪 ⟶ 𝒪_f)` of it, where both hypotheses are theorems rather than assumptions; that case is
`AlgebraicGeometry.RingedSite.derivedSheafHom_awayRestrictScalarsIso` below, and it is where the
tag is registered. -/
noncomputable def derivedSheafHom_restrictScalarsIso
    (X : RingedSite.{u, u, u}) (Oh : Sheaf X.J CommRingCat.{u})
    (f : X.O ⟶ Oh)
    [Epi f] (_hf : AlgebraicGeometry.SheafOfModules.IsFlatMap.{u, u, u} f)
    (L I : CochainComplex (SheafOfModules.{u}
      ((sheafCompose X.J (forget₂ CommRingCat RingCat)).obj Oh)) ℤ)
    [I.IsKInjective] :
    let Xh : RingedSite.{u, u, u} := { C := X.C, J := X.J, O := Oh }
    let R := SheafOfModules.restrictScalars.{u}
      ((sheafCompose X.J (forget₂ CommRingCat RingCat)).map f)
    let LR := (R.mapHomologicalComplex (.up ℤ)).obj L
    let IR := (R.mapHomologicalComplex (.up ℤ)).obj I
    DerivedCategory.Q.obj (sheafHomComplex X LR IR).obj ≅
      DerivedCategory.Q.obj
        ((R.mapHomologicalComplex (.up ℤ)).obj (sheafHomComplex Xh L I).obj) :=
  private_decl% (DerivedCategory.Q.mapIso (comparisonIso X Oh f L I))

/-- The derived comparison is the image of the complex-level comparison isomorphism. -/
private theorem derivedComparison_eq
    (X : RingedSite.{u, u, u}) (Oh : Sheaf X.J CommRingCat.{u})
    (f : X.O ⟶ Oh) [Epi f] (hf : AlgebraicGeometry.SheafOfModules.IsFlatMap.{u, u, u} f)
    (L I : CochainComplex (SheafOfModules.{u}
      ((sheafCompose X.J (forget₂ CommRingCat RingCat)).obj Oh)) ℤ)
    [I.IsKInjective] :
    DerivedCategory.Q.mapIso (comparisonIso X Oh f L I) =
      derivedSheafHom_restrictScalarsIso X Oh f hf L I := rfl

/-- The derived comparison is induced by the map that leaves every local
module homomorphism unchanged. The general helper; the localization case, where epimorphy and
flatness are discharged, is
`AlgebraicGeometry.RingedSite.derivedSheafHom_awayRestrictScalarsIso_canonical`. -/
theorem derivedSheafHom_restrictScalarsIso_canonical
    (X : RingedSite.{u, u, u}) (Oh : Sheaf X.J CommRingCat.{u})
    (f : X.O ⟶ Oh)
    [Epi f] (hf : AlgebraicGeometry.SheafOfModules.IsFlatMap.{u, u, u} f)
    (L I : CochainComplex (SheafOfModules.{u}
      ((sheafCompose X.J (forget₂ CommRingCat RingCat)).obj Oh)) ℤ)
    [I.IsKInjective] :
    let Xh : RingedSite.{u, u, u} := { C := X.C, J := X.J, O := Oh }
    let R := SheafOfModules.restrictScalars.{u}
      ((sheafCompose X.J (forget₂ CommRingCat RingCat)).map f)
    let LR := (R.mapHomologicalComplex (.up ℤ)).obj L
    let IR := (R.mapHomologicalComplex (.up ℤ)).obj I
    ∃ c : (sheafHomComplex X LR IR).obj ≅
        (R.mapHomologicalComplex (.up ℤ)).obj (sheafHomComplex Xh L I).obj,
      (DerivedCategory.Q.mapIso c =
        derivedSheafHom_restrictScalarsIso X Oh f hf L I) ∧
      (∀ (U : X.C) (n p q : ℤ) (hpq : p + n = q)
          (s : ((sheafHomComplex X LR IR).obj.X n).val.obj (op U))
          {W : X.C} (g : W ⟶ U) (x : (L.X p).val.obj (op W)),
        (((AddCommGrpCat.Hom.hom
            (((sheafHomComplex Xh L I).sectionsIso U).hom.f n)
            ((c.hom.f n).val.app (op U) s)).v p q hpq).val.app
              (op (Over.mk g))) x =
          (((AddCommGrpCat.Hom.hom
            (((sheafHomComplex X LR IR).sectionsIso U).hom.f n) s).v p q hpq).val.app
              (op (Over.mk g))) x) :=
  ⟨comparisonIso X Oh f L I, derivedComparison_eq X Oh f hf L I,
    comparisonIso_apply X Oh f L I⟩

/-- Acting on the source and acting on the target by a localized scalar give
the same action on internal Hom. The general helper; the localization case, where epimorphy is
discharged, is
`AlgebraicGeometry.RingedSite.sheafHomComplex_awayLocalizedAction_agree`. -/
theorem sheafHomComplex_localizedAction_agree
    (X : RingedSite.{u, u, u}) (Oh : Sheaf X.J CommRingCat.{u})
    (f : X.O ⟶ Oh)
    [Epi f]
    (L I : CochainComplex (SheafOfModules.{u}
      ((sheafCompose X.J (forget₂ CommRingCat RingCat)).obj Oh)) ℤ) :
    let _Xh : RingedSite.{u, u, u} := { C := X.C, J := X.J, O := Oh }
    let R := SheafOfModules.restrictScalars.{u}
      ((sheafCompose X.J (forget₂ CommRingCat RingCat)).map f)
    let LR := (R.mapHomologicalComplex (.up ℤ)).obj L
    let IR := (R.mapHomologicalComplex (.up ℤ)).obj I
    ∀ (U : X.C) (r : ((sheafCompose X.J (forget₂ CommRingCat RingCat)).obj Oh).obj.obj (op U))
      (n p q : ℤ) (hpq : p + n = q)
      (s : ((sheafHomComplex X LR IR).obj.X n).val.obj (op U))
      {W : X.C} (g : W ⟶ U) (x : (L.X p).val.obj (op W)),
      (((AddCommGrpCat.Hom.hom
        (((sheafHomComplex X LR IR).sectionsIso U).hom.f n) s).v p q hpq).val.app
          (op (Over.mk g)))
            (((L.X p).val.obj (op W)).isModule.smul
              (((sheafCompose X.J (forget₂ CommRingCat RingCat)).obj Oh).obj.map g.op r) x) =
        ((I.X q).val.obj (op W)).isModule.smul
          (((sheafCompose X.J (forget₂ CommRingCat RingCat)).obj Oh).obj.map g.op r)
          (show (I.X q).val.obj (op W) from (((AddCommGrpCat.Hom.hom
            (((sheafHomComplex X LR IR).sectionsIso U).hom.f n) s).v p q hpq).val.app
              (op (Over.mk g))) x) := by
  intro _Xh R LR IR U r n p q hpq s W g x
  let c := comparisonIso X Oh f L I
  let z := (AddCommGrpCat.Hom.hom
    (((sheafHomComplex (localizedSite X Oh) L I).sectionsIso U).hom.f n)
    ((c.hom.f n).val.app (op U) s)).v p q hpq
  have e (y : (L.X p).val.obj (op W)) :=
    comparisonIso_apply X Oh f L I U n p q hpq s g y
  exact (e _).symm.trans (((z.val.app (op (Over.mk g))).hom.map_smul _ x).trans
    (congrArg (fun t ↦ ((I.X q).val.obj (op W)).isModule.smul
      (((sheafCompose X.J (forget₂ CommRingCat RingCat)).obj Oh).obj.map g.op r) t)
      (e x)))

end AlgebraicGeometry.RingedSite
