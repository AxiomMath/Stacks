module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import StacksFrontier.Algebra.Homology.DerivedCategory.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.WeaklyContractible.CohomologyOverAWeaklyContractibleObject
public import StacksFrontier.CategoryTheory.Sites.Modules.GrothendieckAbelianSmall
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.ModuleSections
public import StacksFrontier.CategoryTheory.Sites.WeaklyContractible
public import StacksFrontier.CategoryTheory.Triangulated.CompactObjects
public import StacksFrontier.Homology.KFlat.FilteredColimitShifts
public import StacksFrontier.Homology.Perfect.Characterizing

/-!
# Compact generation of a derived category from quasi-compact weakly contractible objects

Let `(C, J)` be a site and `R` a sheaf of rings on it. Suppose every object of `C` is covered
by objects `U` which are quasi-compact and over which every locally surjective morphism of
sheaves of sets is surjective on sections — the latter being weak contractibility of `U`,
tested in the universe of the module sections. Then the unbounded derived category of sheaves
of `R`-modules is compactly generated.

The generating family consists of the sheafifications `R_U` of the free `R`-module on the
representable presheaf of such a `U`, placed in degree zero. Morphisms out of `R_U` are the
sections over `U` of the target, so quasi-compactness of `U` makes `R_U` a compact object of
the abelian category (sections over a quasi-compact object commute with direct sums) and weak
contractibility makes it projective (sections over a weakly contractible object are exact).
A projective compact object placed in a single degree is a compact object of the derived
category, and the covering hypothesis makes the family of all the `R_U` separating, hence its
images in degree zero a weak triangulated generator.

## Main results

* `Stacks.Cohomology.isCompactlyGenerated_derivedCategory_of_hasEnoughObjects`: the statement
  above, with weak contractibility supplied in the explicit form in which it is tested in the
  universe of the module sections.
* `Stacks.Cohomology.isWeakTriangulatedGenerator_single_of_projective_separating`: the criterion
  behind it — a separating family of projectives, placed in degree zero, is a weak triangulated
  generator of the derived category. It is about an arbitrary abelian category, with no site in
  sight, and is one of the three inputs of any dévissage along compact generators.

## Implementation notes

The generating objects are not required to be weakly contractible in the sense of
`CategoryTheory.GrothendieckTopology.IsWeaklyContractible`, which tests sheaves of sets valued
in the morphism universe of the site, but in the form tested in the universe `max u v w` of the
module sections. The two agree when the objects and the morphisms of the site lie in the same
universe; when the objects exceed the morphisms — as for a site of schemes — the module
universe is strictly larger, and the stronger form is what the proof consumes. This is also
the form in which `Stacks.WeaklyContractible.exact_sheafSections_of_isWeaklyContractible`
(Stacks 0946 part (1)) takes its hypothesis, and no smallness of the site is needed anywhere.

The abelian category of sheaves of modules is Grothendieck abelian in the universe
`max u v w` by `Stacks.SheafOfModules.Small.isGrothendieckAbelian_sheafOfModules`, which is
what supplies both the K-projective resolutions behind
`isCompactObject_derived_single` and the commutation of `Q : C(A) ⥤ D(A)` with arbitrary
direct sums of that universe.

## References

* [Stacks Project, Tag 0F4Q](https://stacks.math.columbia.edu/tag/0F4Q)
* [Stacks Project, Tag 094E](https://stacks.math.columbia.edu/tag/094E)
* [Stacks Project, Tag 0946](https://stacks.math.columbia.edu/tag/0946)
* [Stacks Project, Tag 0935](https://stacks.math.columbia.edu/tag/0935)
* [Stacks Project, Tag 09SQ](https://stacks.math.columbia.edu/tag/09SQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped DirectSum

universe z s t u v w

namespace Stacks.Cohomology

attribute [local instance] HasDerivedCategory.standard

/-! ### A single projective compact object generates in degree zero -/

section SingleFunctor

/-- A separating family of projective objects, placed in degree zero, is a weak triangulated
generator of the derived category: an object receiving only zero maps from all shifts of the
family has vanishing homology, because a nonzero homology class would be detected by a map
from a member of the family, which projectivity lifts to a map of complexes.

The criterion is about an arbitrary abelian category with a model of its derived category, and
the family it is applied to need not come from a site; it is therefore public, being one of the
three inputs that a dévissage along compact generators needs. -/
public theorem isWeakTriangulatedGenerator_single_of_projective_separating
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{z} A]
    {ι : Type t} (P : ι → A) [∀ i, Projective (P i)]
    (hsep : (ObjectProperty.ofObj P).IsSeparating) :
    (ObjectProperty.ofObj (fun i ↦
      (DerivedCategory.singleFunctor A 0).obj (P i))).IsWeakTriangulatedGenerator := by
  intro K hK
  let L := DerivedCategory.Q.objPreimage K
  let e := DerivedCategory.Q.objObjPreimageIso K
  apply StacksDraft.Perfect.isZero_of_homology_isZero K
  intro n
  have hL : IsZero (L.homology n) := by
    apply (IsZero.iff_id_eq_zero _).2
    apply hsep
    intro G hG g
    simp only [ObjectProperty.ofObj_iff] at hG
    rcases hG with ⟨i, rfl⟩
    let a := Projective.factorThru g (L.homologyπ n)
    let φ : (CochainComplex.singleFunctor A n).obj (P i) ⟶ L :=
      HomologicalComplex.mkHomFromSingle (a ≫ L.iCycles n) (fun j _ ↦ by simp)
    have hφ : DerivedCategory.Q.map φ = 0 := by
      apply (cancel_mono e.hom).1
      rw [zero_comp]
      apply hK
      refine ⟨(DerivedCategory.singleFunctor A 0).obj (P i), -n, ?_, by simp⟩
      exact (((DerivedCategory.singleFunctors A).shiftIso (-n) n 0 (by omega)).app (P i)).symm
    have hc : HomologicalComplex.cyclesMap φ n =
        (HomologicalComplex.singleObjCyclesSelfIso (.up ℤ) n (P i)).hom ≫ a := by
      apply (cancel_mono (L.iCycles n)).1
      simp [φ, HomologicalComplex.cyclesMap_i,
        HomologicalComplex.singleObjCyclesSelfIso_hom, Category.assoc]
    have hg : (HomologicalComplex.singleObjCyclesSelfIso (.up ℤ) n (P i)).hom ≫ g = 0 := by
      rw [← Projective.factorThru_comp g (L.homologyπ n), ← Category.assoc,
        ← hc, ← HomologicalComplex.homologyπ_naturality,
        StacksDraft.Perfect.homologyMap_eq_zero_of_Q_map_eq_zero φ hφ n, comp_zero]
    exact (cancel_epi (HomologicalComplex.singleObjCyclesSelfIso (.up ℤ) n (P i)).hom).1
      (by simpa using hg)
  exact hL.of_iso ((DerivedCategory.homologyFunctor A n).mapIso e.symm ≪≫
    (DerivedCategory.homologyFunctorFactors A n).app L)

/-- A projective object placed in a single degree gives a K-projective complex. -/
private theorem isKProjective_single
    {A : Type u} [Category.{v} A] [Abelian A] (P : A) [Projective P] (n : ℤ) :
    ((CochainComplex.singleFunctor A n).obj P).IsKProjective := by
  have (i : ℤ) : Projective (((CochainComplex.singleFunctor A n).obj P).X i) := by
    by_cases hi : i = n
    · subst i
      exact Projective.of_iso (HomologicalComplex.singleObjXSelf (.up ℤ) n P).symm
        inferInstance
    · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) n P i hi).projective
  exact CochainComplex.isKProjective_of_projective _ n


/-- A projective compact object of a Grothendieck abelian category, placed in a single degree,
is a compact object of the derived category. -/
private theorem isCompactObject_derived_single
    {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{t} A]
    [HasDerivedCategory.{z} A]
    (P : A) [Projective P] [IsCompactObject.{t} P] (n : ℤ) :
    IsCompactObject.{t} ((DerivedCategory.singleFunctor A n).obj P) := by
  have := StacksDraft.Perfect.isKProjective_single P n
  have := StacksDraft.Perfect.isCompactObject_cochain_single P n
  have := fun I : Type t ↦
    CochainComplex.KFlat.CoproductBridge.preservesCoproducts_Q_of_grothendieck (A := A) I
  exact StacksDraft.Perfect.isCompactObject_map_of_map_surjective DerivedCategory.Q _
    (fun Y ↦ StacksDraft.Perfect.map_surjective_of_isKProjective _ Y)

end SingleFunctor

/-- A colimit cofan of abelian groups is spanned by the direct sum of its legs. -/
private lemma surjective_directSum_of_isColimit {I : Type t} [DecidableEq I]
    {E : I → AddCommGrpCat.{t}} {S : AddCommGrpCat.{t}}
    (ι : ∀ i, E i ⟶ S) (hc : IsColimit (Cofan.mk S ι)) :
    Function.Surjective (DirectSum.toAddMonoid fun i ↦ (ι i).hom) := by
  let D := AddCommGrpCat.of (⨁ i, E i)
  let d : Cofan E :=
    Cofan.mk D (fun i ↦ AddCommGrpCat.ofHom (DirectSum.of (fun j ↦ (E j : Type t)) i))
  let f : D ⟶ S := AddCommGrpCat.ofHom (DirectSum.toAddMonoid fun i ↦ (ι i).hom)
  let g : S ⟶ D := hc.desc d
  have hgf : g ≫ f = 𝟙 S := by
    apply hc.hom_ext
    rintro ⟨i⟩
    change ι i ≫ g ≫ f = ι i ≫ 𝟙 S
    have hi : ι i ≫ g = d.inj i := hc.fac d ⟨i⟩
    rw [← Category.assoc, hi]
    ext x
    exact DirectSum.toAddMonoid_of (fun j ↦ (ι j).hom) i x
  exact fun x ↦ ⟨g x, ConcreteCategory.congr_hom hgf x⟩

/-! ### The free module on a representable -/

section Site

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (R : Sheaf J RingCat.{max u v w})
    [HasSheafify J AddCommGrpCat.{max u v w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]

/-- The sheafification of the free module presheaf on the representable at `U`; the sheaf of
`R`-modules whose sections over an object are the free modules on the morphisms into `U`. -/
private abbrev freeSheafOnObject (U : C) :=
  (PresheafOfModules.sheafification (𝟙 R.obj)).obj
    ((PresheafOfModules.free R.obj).obj (uliftYoneda.{max u w}.obj U))

/-- Morphisms out of `freeSheafOnObject J R U` are the sections of the target over `U`. -/
private def freeSheafOnObjectHomEquiv (U : C)
    (M : SheafOfModules.{max u v w} R) :
    (freeSheafOnObject J R U ⟶ M) ≃ (M.val.obj (op U) : Type (max u v w)) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv _ M).trans
    (PresheafOfModules.freeHomEquiv.trans uliftYonedaEquiv)

private lemma freeSheafOnObjectHomEquiv_naturality (U : C)
    {M N : SheafOfModules.{max u v w} R}
    (f : freeSheafOnObject J R U ⟶ M) (g : M ⟶ N) :
    freeSheafOnObjectHomEquiv J R U N (f ≫ g) =
      g.val.app (op U) (freeSheafOnObjectHomEquiv J R U M f) := rfl

/-- The bijection of `freeSheafOnObjectHomEquiv` is additive. -/
private def freeSheafOnObjectHomAddEquiv (U : C)
    (M : SheafOfModules.{max u v w} R) :
    (freeSheafOnObject J R U ⟶ M) ≃+ (M.val.obj (op U) : Type (max u v w)) where
  __ := freeSheafOnObjectHomEquiv J R U M
  map_add' f g := by
    have he (N : SheafOfModules.{max u v w} R) (k : freeSheafOnObject J R U ⟶ N) :=
      freeSheafOnObjectHomEquiv_naturality J R U (𝟙 (freeSheafOnObject J R U)) k
    simp only [Category.id_comp] at he
    change freeSheafOnObjectHomEquiv J R U M (f + g) =
      freeSheafOnObjectHomEquiv J R U M f + freeSheafOnObjectHomEquiv J R U M g
    rw [he M (f + g), he M f, he M g]
    rfl

/-- Over a quasi-compact object the free module sheaf is a compact object of the abelian
category of sheaves of modules: its morphism groups are the sections over that object, which
commute with direct sums by Stacks 0935 part (2). -/
private lemma isCompactObject_freeSheafOnObject (U : C) (hU : J.IsQuasiCompactObject U) :
    IsCompactObject.{max u v w} (freeSheafOnObject J R U) := by
  classical
  constructor
  intro I _ E _
  refine ⟨CategoryTheory.injective_cofanMap _ (Sigma.ι E) (coproductIsCoproduct E), ?_⟩
  intro f
  let S := SheafOfModules.toSheaf R ⋙
    (sheafSections J AddCommGrpCat.{max u v w}).obj (op U)
  have : PreservesColimitsOfShape (Discrete I) S :=
    Stacks.Sites.sheafOfModules_sections_preserves_coproducts J R U hU I
  have hc : IsColimit (Cofan.mk (S.obj (∐ E)) (fun i ↦ S.map (Sigma.ι E i))) :=
    (isColimitMapCoconeCofanMkEquiv S E (Sigma.ι E))
      (isColimitOfPreserves S (coproductIsCoproduct E))
  let e (M : SheafOfModules.{max u v w} R) := freeSheafOnObjectHomAddEquiv J R U M
  obtain ⟨x, hx⟩ := surjective_directSum_of_isColimit _ hc (e (∐ E) f)
  change (⨁ i, (E i).val.obj (op U)) at x
  change DirectSum.toAddMonoid
    (fun i ↦ ((Sigma.ι E i).val.app (op U)).hom.toAddMonoidHom) x = e (∐ E) f at hx
  let y := DirectSum.map (fun i ↦ (e (E i)).symm.toAddMonoidHom) x
  refine ⟨y, ?_⟩
  apply (e (∐ E)).injective
  change e (∐ E) (DirectSum.toAddMonoid
    (fun i ↦ Preadditive.rightComp (freeSheafOnObject J R U) (Sigma.ι E i)) y) = _
  rw [← hx]
  dsimp only [y]
  clear hx y
  induction x using DirectSum.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | of i g =>
    simp only [DirectSum.map_of, DirectSum.toAddMonoid_of]
    change freeSheafOnObjectHomEquiv J R U (∐ E)
      ((e (E i)).symm g ≫ Sigma.ι E i) = _
    rw [freeSheafOnObjectHomEquiv_naturality]
    change (S.map (Sigma.ι E i)).hom (e (E i) ((e (E i)).symm g)) = _
    rw [AddEquiv.apply_symm_apply]
    rfl

/-- Over an object on which locally surjective morphisms of sheaves of sets are surjective,
an epimorphism of sheaves of modules is surjective on sections. -/
private lemma sections_surjective_of_epi_on_weaklyContractible (U : C)
    (hU : ∀ (F G : Sheaf J (Type (max u v w))) (φ : F ⟶ G),
      Sheaf.IsLocallySurjective φ → Function.Surjective (φ.hom.app (op U)))
    {M N : SheafOfModules.{max u v w} R} (f : M ⟶ N) [Epi f] :
    Function.Surjective (fun x : M.val.obj (Opposite.op U) ↦
      f.val.app (Opposite.op U) x) := by
  let sections := (sheafSections J AddCommGrpCat.{max u v w}).obj (op U)
  have hexact : exactFunctor (Sheaf J AddCommGrpCat.{max u v w}) AddCommGrpCat.{max u v w}
      ((sheafSections J AddCommGrpCat.{max u v w}).obj (op U)) :=
    Stacks.WeaklyContractible.exact_sheafSections_of_isWeaklyContractible J U hU
  have : PreservesFiniteColimits sections := ((exactFunctor_iff sections).1 hexact).2
  have : Epi ((SheafOfModules.toSheaf.{max u v w} R).map f) :=
    preserves_epi_of_preservesColimit (SheafOfModules.toSheaf.{max u v w} R) f
  have hmap : Epi (sections.map ((SheafOfModules.toSheaf.{max u v w} R).map f)) :=
    preserves_epi_of_preservesColimit sections _
  have hsurj : Function.Surjective
      (ConcreteCategory.hom (sections.map ((SheafOfModules.toSheaf.{max u v w} R).map f))) :=
    (AddCommGrpCat.epi_iff_surjective _).1 hmap
  exact hsurj

/-- Over an object on which locally surjective morphisms of sheaves of sets are surjective,
the free module sheaf is projective: lifting a morphism out of it along an epimorphism is
lifting a section along a surjection. -/
private lemma projective_freeSheafOnObject_of_isWeaklyContractible (U : C)
    (hU : ∀ (F G : Sheaf J (Type (max u v w))) (φ : F ⟶ G),
      Sheaf.IsLocallySurjective φ → Function.Surjective (φ.hom.app (op U))) :
    Projective (freeSheafOnObject J R U) := by
  refine Projective.mk ?_
  intro M N g f hf
  let eM := freeSheafOnObjectHomEquiv J R U M
  let eN := freeSheafOnObjectHomEquiv J R U N
  obtain ⟨s, hs⟩ := sections_surjective_of_epi_on_weaklyContractible J R U hU f (eN g)
  refine ⟨eM.symm s, ?_⟩
  apply eN.injective
  rw [freeSheafOnObjectHomEquiv_naturality]
  change f.val.app (op U) (eM (eM.symm s)) = eN g
  simpa only [Equiv.apply_symm_apply] using hs

/-- If every object of the site is covered by objects with the property `P`, then the free
module sheaves on the objects with `P` form a separating family. -/
private lemma isSeparating_freeSheavesOnObjects (P : ObjectProperty C)
    (hEnough : ∀ T : C, ∃ (I : Type s) (V : I → C) (p : ∀ i, V i ⟶ T),
      Sieve.ofArrows V p ∈ J T ∧ ∀ i, P (V i)) :
    (ObjectProperty.ofObj (fun i : {U : C // P U} ↦ freeSheafOnObject J R i.1)).IsSeparating := by
  classical
  intro M N f g hfg
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  cases U with
  | op T =>
    apply ModuleCat.hom_ext
    ext s
    obtain ⟨I, V, p, hpCover, hp⟩ := hEnough T
    apply N.isSheaf.isSeparated T (Sieve.ofArrows V p) hpCover
    intro W q hq
    obtain ⟨i, a, ha⟩ := (Sieve.mem_ofArrows_iff V p q).1 hq
    let j : {U : C // P U} := ⟨V i, hp i⟩
    let eM := freeSheafOnObjectHomEquiv J R j.1 M
    let eN := freeSheafOnObjectHomEquiv J R j.1 N
    let t : M.val.obj (op (V i)) := M.val.map (p i).op s
    let k := eM.symm t
    have hE : ObjectProperty.ofObj (fun j : {U : C // P U} ↦ freeSheafOnObject J R j.1)
        (freeSheafOnObject J R j.1) := by
      rw [ObjectProperty.ofObj_iff]
      exact ⟨j, rfl⟩
    have hk' := congrArg eN (hfg (freeSheafOnObject J R j.1) hE k)
    rw [freeSheafOnObjectHomEquiv_naturality,
      freeSheafOnObjectHomEquiv_naturality] at hk'
    have hkvalue : eM k = t := Equiv.apply_symm_apply eM t
    rw [hkvalue] at hk'
    change f.val.app (op (V i)) (M.val.map (p i).op s) =
      g.val.app (op (V i)) (M.val.map (p i).op s) at hk'
    have hf := ConcreteCategory.congr_hom (f.val.naturality (p i).op) s
    have hg := ConcreteCategory.congr_hom (g.val.naturality (p i).op) s
    simp only [CategoryTheory.comp_apply, ModuleCat.restrictScalars.map_apply] at hf hg
    have hkq := congrArg (fun z ↦ N.val.map a.op z) hk'
    rw [hf, hg] at hkq
    have hcomp (x : N.val.obj (op T)) :
        N.val.map q.op x = N.val.map a.op (N.val.map (p i).op x) := by
      rw [ha, CategoryTheory.op_comp]
      exact N.val.map_comp_apply (p i).op a.op x
    change N.val.map q.op (f.val.app (op T) s) =
      N.val.map q.op (g.val.app (op T) s)
    rw [hcomp, hcomp]
    exact hkq

end Site

/-- **Compact generation of the derived category of a ringed site with enough quasi-compact
weakly contractible objects.** Let `R` be a sheaf of rings on a site `(C, J)` and let `P` be a
property of objects such that every object of `C` is covered by objects with `P`, every object
with `P` is quasi-compact, and over every object with `P` a locally surjective morphism of
sheaves of sets valued in the module universe is surjective on sections. Then the unbounded
derived category of sheaves of `R`-modules is compactly generated.

The generating family is the free module sheaves on the representables of the objects with `P`,
placed in degree zero: quasi-compactness makes them compact, the surjectivity makes them
projective, and the covering hypothesis makes them separating. -/
theorem isCompactlyGenerated_derivedCategory_of_hasEnoughObjects
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (R : Sheaf J RingCat.{max u v w})
    [HasSheafify J AddCommGrpCat.{max u v w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    (P : ObjectProperty C)
    (hqc : ∀ U : C, P U → J.IsQuasiCompactObject U)
    (hwc : ∀ U : C, P U → ∀ (F G : Sheaf J (Type (max u v w))) (φ : F ⟶ G),
      Sheaf.IsLocallySurjective φ → Function.Surjective (φ.hom.app (op U)))
    (hEnough : ∀ T : C, ∃ (I : Type s) (V : I → C) (p : ∀ i, V i ⟶ T),
      Sieve.ofArrows V p ∈ J T ∧ ∀ i, P (V i)) :
    Pretriangulated.IsCompactlyGenerated.{max u v w}
      (DerivedCategory (SheafOfModules.{max u v w} R)) := by
  classical
  let ι := ULift.{max u v w} {U : C // P U}
  let Q : ι → SheafOfModules.{max u v w} R := fun i ↦ freeSheafOnObject J R i.down.1
  let E := fun i ↦ (DerivedCategory.singleFunctor (SheafOfModules.{max u v w} R) 0).obj (Q i)
  have hs : (ObjectProperty.ofObj Q).IsSeparating := by
    convert isSeparating_freeSheavesOnObjects J R P hEnough using 1
    ext M
    simp only [ObjectProperty.ofObj_iff]
    exact ⟨fun ⟨i, hi⟩ ↦ ⟨i.down, hi⟩, fun ⟨i, hi⟩ ↦ ⟨ULift.up i, hi⟩⟩
  have hp (i : ι) : Projective (Q i) :=
    projective_freeSheafOnObject_of_isWeaklyContractible J R i.down.1 (hwc _ i.down.2)
  refine ⟨ι, E, fun i ↦ ?_, isWeakTriangulatedGenerator_single_of_projective_separating Q hs⟩
  have : IsCompactObject.{max u v w} (Q i) :=
    isCompactObject_freeSheafOnObject J R i.down.1 (hqc _ i.down.2)
  exact isCompactObject_derived_single (Q i) 0

/-- **Compact generation of the derived category of a ringed site with enough quasi-compact
weakly contractible objects**, with the covering hypothesis in the form
`CategoryTheory.GrothendieckTopology.HasEnoughObjects`.

This is `isCompactlyGenerated_derivedCategory_of_hasEnoughObjects` specialized to covering
families indexed by the morphism universe of the site; the general form is needed on a site
whose objects live above its morphisms, where the available covering families are indexed by
the universe of the objects. -/
theorem isCompactlyGenerated_derivedCategory_of_hasEnoughObjects'
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (R : Sheaf J RingCat.{max u v w})
    [HasSheafify J AddCommGrpCat.{max u v w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    (P : ObjectProperty C)
    (hqc : ∀ U : C, P U → J.IsQuasiCompactObject U)
    (hwc : ∀ U : C, P U → ∀ (F G : Sheaf J (Type (max u v w))) (φ : F ⟶ G),
      Sheaf.IsLocallySurjective φ → Function.Surjective (φ.hom.app (op U)))
    (hEnough : J.HasEnoughObjects P) :
    Pretriangulated.IsCompactlyGenerated.{max u v w}
      (DerivedCategory (SheafOfModules.{max u v w} R)) :=
  isCompactlyGenerated_derivedCategory_of_hasEnoughObjects J R P hqc hwc hEnough

end Stacks.Cohomology

end
