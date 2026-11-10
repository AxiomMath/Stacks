module

public import Mathlib
public import StacksFrontier.Algebra.Homology.Resolution.ProjectiveResolution
public import StacksFrontier.Algebra.Module.Projective.Nakayama
public import StacksFrontier.Algebra.Module.Projective.StablyFreeLift
public import StacksFrontier.Homology.LiftAcyclicComplex
public import StacksFrontier.Homology.PseudoCoherent.Characterization
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Lifting a complex across a quotient

Let `I` be an ideal of a commutative ring `R`. Reduction modulo `I` is realized here as extension
of scalars along `R → R ⧸ I`, and its derived version as the total left derived functor of that
extension, namely the canonical datum
`CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars` of [stacks 064H]. This
module reverses that passage: a bounded above complex of `R ⧸ I`-modules representing the derived
reduction of an object `K` of `D(R)` is, under suitable hypotheses on its terms, the reduction of
a bounded above complex of `R`-modules representing `K` itself.

The result is proved for an abstract class `P` of projective `R`-modules which is closed under
finite direct sums and complementary summands and which detects surjectivity modulo `I`.
Instantiating `P` at finite stably free modules, at finite projective modules over a henselian
pair, or at projective modules over a nilpotent quotient yields the corresponding lifting
theorems; the finite stably free instance is carried out here.

## Main results

* `StacksDraft.Perfect.exists_boundedAbove_lift_representing` ([stacks 0BCA]): the lifting
  theorem for an abstract class `P` of projective modules.
* `StacksDraft.Perfect.exists_boundedAbove_lift_representing_of_datum`: its general form, stated
  for an arbitrary total derived extension-of-scalars datum rather than the canonical one.
* `StacksDraft.Perfect.exists_boundedAbove_lift_representing_iso`: the refinement in which a
  *prescribed* derived identification of the given complex with the reduction of `K` is lifted
  together with the complex, so that the comparison square commutes on the nose. This is the form
  the consumers of the theorem need, since they have to propagate a chosen identification through
  an induction.
* `StacksDraft.Perfect.exists_boundedAbove_isStablyFree_lift_representing` ([stacks 0BCB]): the
  instance of the lifting theorem at the class of finite stably free modules, for an ideal
  contained in the Jacobson radical and a pseudo-coherent object, together with the assertion that
  freeness of a term of the given complex is inherited by the corresponding term of the lift.
* `StacksDraft.Perfect.exists_boundedAbove_isStablyFree_lift_representing_of_datum`: its general
  form, for an arbitrary datum.
* `StacksDraft.Perfect.exists_boundedAbove_isStablyFree_lift_representing_iso`: its refinement
  lifting a prescribed derived identification, as for [stacks 0BCA].

## Implementation notes

The quotient `P / IP` is expressed as extension of scalars from `R` to `R ⧸ I`. Thus the given
complex and the reduction of a lifted complex are complexes of actual `R ⧸ I`-modules, and an
identification between them is an isomorphism of complexes, hence compatible with every
differential. Representation of an object of a derived category by a complex is an isomorphism
from the image of the complex under the localization functor, and the conclusions are existential
rather than data-valued: the lifted complex is not canonical.

The source statements are about *the* derived reduction, so the tagged results are stated for the
canonical datum. Only the comparison natural transformation carried by that datum enters the
proofs, however, so each is factored through a general form quantifying over an arbitrary total
derived extension-of-scalars datum, which is therefore applicable to any construction of
`- ⊗ᴸ_R R/I`. These general forms, and the refinements which lift a prescribed derived
identification, carry the datum as an explicit argument and are untagged.

The lift is built as a shift of the cokernel of a map into an acyclic lift of a mapping cone. The
acyclic lift is `LiftAcyclic.exists_lift_acyclic_complex`, used at the same module universe as the
given complex; the mapping cone is the cone on the quasi-isomorphism which realizes the prescribed
derived identification, available because a bounded above complex whose terms are reductions of
projectives is K-projective.

Ring and module universes are kept independent: `R : Type u` and modules in `ModuleCat.{max v u}`.

Stable freeness is Mathlib's `Module.IsStablyFree`: the existence of a finite free complement
making a direct sum free. Together with `Module.Finite` this is the Stacks Project's class of
finite stably free modules, and the two-out-of-three property those modules enjoy is proved here
directly in that formulation, the ambient module being finite so that both complements of a
splitting are again finite free.

## References

* [Stacks Project, Tag 0BCA](https://stacks.math.columbia.edu/tag/0BCA)
* [Stacks Project, Tag 0BCB](https://stacks.math.columbia.edu/tag/0BCB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CochainComplex.DerivedExtensionScalars

open scoped TensorProduct ZeroObject

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace StacksDraft.Perfect

/-! ### Lifting a complex representing a derived reduction -/

section BoundedAboveLift

/-- A bounded above complex of `R ⧸ I`-modules whose terms are reductions of projective
`R`-modules is K-projective. -/
private theorem isKProjective_of_reduction_terms
    {R : Type u} [CommRing R] (I : Ideal R)
    (P : ModuleCat.{max v u} R → Prop)
    (E : CochainComplex (ModuleCat.{max v u} (R ⧸ I)) ℤ)
    (hprojective : ∀ M, P M → Module.Projective R M)
    (hbdd : ∃ b, E.IsStrictlyLE b)
    (hterms : ∀ i, ∃ M, P M ∧ Nonempty
      (E.X i ≅
        (ModuleCat.extendScalars.{u, u, max v u} (Ideal.Quotient.mk I)).obj M)) :
    E.IsKProjective := by
  obtain ⟨b, hb⟩ := hbdd
  have : E.IsStrictlyLE b := hb
  have htermProjective (i : ℤ) : Projective (E.X i) := by
    obtain ⟨M, hM, ⟨e⟩⟩ := hterms i
    have : Module.Projective R M := hprojective M hM
    have : Projective M := inferInstance
    have hFM : Projective
        ((ModuleCat.extendScalars.{u, u, max v u} (Ideal.Quotient.mk I)).obj M) :=
      (ModuleCat.extendRestrictScalarsAdj (Ideal.Quotient.mk I)).map_projective M inferInstance
    exact Projective.of_iso e.symm hFM
  exact CochainComplex.isKProjective_of_projective E b

/-- An isomorphism in the derived category out of a K-projective complex is realized by an
honest quasi-isomorphism of complexes. -/
@[sga "6 II 1.2" "1.2 d), special case"]
private theorem exists_quasiIso_of_derived_iso
    {A : Type*} [Category A] [Abelian A]
    [HasDerivedCategory A]
    (E L : CochainComplex A ℤ) [E.IsKProjective]
    (e : (DerivedCategory.Q).obj E ≅ (DerivedCategory.Q).obj L) :
    ∃ δ : E ⟶ L, QuasiIso δ ∧ (DerivedCategory.Q).map δ = e.hom := by
  obtain ⟨β, hβ⟩ := (CochainComplex.IsKProjective.Qh_map_bijective E
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L)).surjective
    ((DerivedCategory.quotientCompQhIso A).hom.app E ≫ e.hom ≫
      (DerivedCategory.quotientCompQhIso A).inv.app L)
  obtain ⟨δ, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective β
  have h := DerivedCategory.quotientCompQhIso_hom_naturality (C := A) δ
  rw [hβ] at h
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id] at h
  have hQ : (DerivedCategory.Q).map δ = e.hom :=
    ((cancel_epi ((DerivedCategory.quotientCompQhIso A).hom.app E)).1 h).symm
  refine ⟨δ, ?_, hQ⟩
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso, hQ]
  infer_instance

/-- The restriction of the extension of scalars of `M` along `R → R ⧸ I` is `M / IM`. -/
private noncomputable abbrev reductionRestrictIso
    {R : Type u} [CommRing R] (I : Ideal R) (M : ModuleCat.{max v u} R) :
    (ModuleCat.restrictScalars.{max v u} (Ideal.Quotient.mk I)).obj
        ((ModuleCat.extendScalars.{u, u, max v u} (Ideal.Quotient.mk I)).obj M) ≅
      ModuleCat.of R (M ⧸ (I • (⊤ : Submodule R M))) :=
  LinearEquiv.toModuleIso (TensorProduct.quotTensorEquivQuotSMul M I)

/-- A map between modules in a class of projectives detecting surjectivity through `F` is an
isomorphism as soon as its image under `F` is. -/
private theorem isIso_of_isIso_map
    {R S : Type*} [Ring R] [Ring S]
    (F : ModuleCat R ⥤ ModuleCat S) (P : ModuleCat R → Prop)
    (hprojective : ∀ M, P M → Module.Projective R M)
    (hsurjective : ∀ (M N : ModuleCat R) (f : M ⟶ N), P M → P N →
      Function.Surjective (F.map f).hom → Function.Surjective f.hom)
    {M N : ModuleCat R} (hM : P M) (hN : P N) (f : M ⟶ N)
    [IsIso (F.map f)] : IsIso f := by
  have hfSurj : Function.Surjective f.hom := hsurjective M N f hM hN
    ((ModuleCat.epi_iff_surjective (F.map f)).1 inferInstance)
  have : Epi f := (ModuleCat.epi_iff_surjective f).2 hfSurj
  have : Module.Projective R N := hprojective N hN
  have : Projective N := inferInstance
  let s : N ⟶ M := Projective.factorThru (𝟙 N) f
  have hs : s ≫ f = 𝟙 N := Projective.factorThru_comp (𝟙 N) f
  have hFs : F.map s ≫ F.map f = 𝟙 _ := by
    simp only [← F.map_comp, hs, F.map_id]
  have hFf : F.map f ≫ F.map s = 𝟙 _ := by
    rw [IsIso.eq_inv_of_inv_hom_id hFs]
    exact IsIso.hom_inv_id _
  have hFfs : F.map (f ≫ s) = 𝟙 _ := by
    simpa only [F.map_comp] using hFf
  have hfsSurj : Function.Surjective (F.map (f ≫ s)).hom := by
    rw [hFfs]
    exact fun y => ⟨y, rfl⟩
  have : Epi (f ≫ s) := (ModuleCat.epi_iff_surjective (f ≫ s)).2
    (hsurjective M M (f ≫ s) hM hM hfsSurj)
  have hfs : f ≫ s = 𝟙 M := (cancel_epi (f ≫ s)).mp (by simp [reassoc_of% hs])
  exact ⟨⟨s, hfs, hs⟩⟩

/-- The unit `M ⟶ M / IM` of the extension-restriction adjunction is an epimorphism. -/
private theorem reductionUnit_epi
    {R : Type u} [CommRing R] (I : Ideal R) (M : ModuleCat.{max v u} R) :
    Epi ((ModuleCat.extendRestrictScalarsAdj (Ideal.Quotient.mk I)).unit.app M) := by
  let e := reductionRestrictIso I M
  have h : (ModuleCat.extendRestrictScalarsAdj (Ideal.Quotient.mk I)).unit.app M ≫ e.hom =
      ModuleCat.ofHom (Submodule.mkQ (I • (⊤ : Submodule R M))) := by
    ext x
    change TensorProduct.quotTensorEquivQuotSMul M I ((1 : R ⧸ I) ⊗ₜ[R] x) = _
    simp
  have : Epi ((ModuleCat.extendRestrictScalarsAdj (Ideal.Quotient.mk I)).unit.app M ≫ e.hom) := by
    rw [h]
    exact (ModuleCat.epi_iff_surjective _).2 (Submodule.mkQ_surjective _)
  exact (epi_comp_iff_of_isIso _ e.hom).1 inferInstance

/-- A map between the reductions of modules lifts to a map of modules as soon as the source is
projective. -/
private theorem exists_reduction_map
    {R : Type u} [CommRing R] (I : Ideal R)
    {M N : ModuleCat.{max v u} R} [Projective M]
    (f : (ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj M ⟶
      (ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj N) :
    ∃ g : M ⟶ N, (ModuleCat.extendScalars (Ideal.Quotient.mk I)).map g = f := by
  let adj := ModuleCat.extendRestrictScalarsAdj (Ideal.Quotient.mk I)
  have := reductionUnit_epi I N
  let g := Projective.factorThru (adj.homEquiv _ _ f) (adj.unit.app N)
  refine ⟨g, adj.homEquiv _ _ |>.injective ?_⟩
  rw [adj.homEquiv_unit]
  exact (adj.unit.naturality g).symm.trans (Projective.factorThru_comp _ _)

/-- Extension of scalars along `R → R ⧸ I` preserves binary biproducts. -/
private noncomputable instance reduction_preservesBinaryBiproducts
    {R : Type u} [CommRing R] (I : Ideal R) :
    PreservesBinaryBiproducts
      (ModuleCat.extendScalars.{u, u, max v u} (Ideal.Quotient.mk I)) :=
  preservesBinaryBiproducts_of_preservesBinaryCoproducts _

/-- Extension of scalars along `R → R ⧸ I` is additive. -/
private noncomputable instance reduction_additive
    {R : Type u} [CommRing R] (I : Ideal R) :
    (ModuleCat.extendScalars.{u, u, max v u} (Ideal.Quotient.mk I)).Additive :=
  Functor.additive_of_preservesBinaryBiproducts _

/-- A splitting of the reduction of `f` off a reduced summand lifts to a splitting of `f`
itself. -/
private theorem exists_biprod_iso_of_reduction
    {R : Type u} [CommRing R] (I : Ideal R)
    (P : ModuleCat.{max v u} R → Prop)
    (hp : ∀ M, P M → Module.Projective R M)
    (hsum : ∀ M N, P M → P N → P (M ⊞ N))
    (hs : ∀ (M N : ModuleCat.{max v u} R) (f : M ⟶ N), P M → P N →
      Function.Surjective ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).map f).hom →
      Function.Surjective f.hom)
    {M N T : ModuleCat.{max v u} R} (hM : P M) (hN : P N) (hT : P T)
    (f : M ⟶ N)
    (e : (ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj M ⊞
      (ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj T ≅
      (ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj N)
    (he : biprod.inl ≫ e.hom = (ModuleCat.extendScalars (Ideal.Quotient.mk I)).map f) :
    ∃ a : M ⊞ T ≅ N, biprod.inl ≫ a.hom = f := by
  let F := ModuleCat.extendScalars (Ideal.Quotient.mk I)
  have : Module.Projective R T := hp T hT
  have : Projective T := inferInstance
  obtain ⟨g, hg⟩ := exists_reduction_map I (biprod.inr ≫ e.hom)
  let a := biprod.desc f g
  have ha : F.map a = (F.mapBiprod M T).hom ≫ e.hom := by
    rw [← biprod.mapBiprod_hom_desc]
    congr 1
    apply biprod.hom_ext'
    · simpa only [biprod.inl_desc] using he.symm
    · simpa only [biprod.inr_desc] using hg
  have : IsIso (F.map a) := by rw [ha]; infer_instance
  have : IsIso a := isIso_of_isIso_map F P hp hs (hsum M T hM hT) hN a
  exact ⟨asIso a, by simp [a]⟩

/-- A map between acyclic complexes is a quasi-isomorphism. -/
private theorem quasiIso_of_exact
    {C : Type*} [Category C] [Abelian C]
    {A B : CochainComplex C ℤ} (f : A ⟶ B)
    (hA : ∀ i, A.ExactAt i) (hB : ∀ i, B.ExactAt i) : QuasiIso f := by
  constructor
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact IsZero.isIso (hA i).isZero_homology (hB i).isZero_homology _

/-- A map from the reduction of a K-projective complex with projective terms into the reduction
of an acyclic complex lifts to a map of complexes. -/
private theorem exists_complex_map_of_reduction
    {R : Type u} [CommRing R] (I : Ideal R)
    (K A : CochainComplex (ModuleCat.{max v u} R) ℤ)
    [K.IsKProjective] [∀ i, Projective (K.X i)]
    (hA : ∀ i, A.ExactAt i)
    (hFA : ∀ i, (((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj A).ExactAt i)
    (f : ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K ⟶
      ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj A) :
    ∃ g : K ⟶ A, ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map g = f := by
  let F := ModuleCat.extendScalars (Ideal.Quotient.mk I)
  let G := ModuleCat.restrictScalars (Ideal.Quotient.mk I)
  let FC := F.mapHomologicalComplex (ComplexShape.up ℤ)
  let GC := G.mapHomologicalComplex (ComplexShape.up ℤ)
  let adj := ModuleCat.extendRestrictScalarsAdj (Ideal.Quotient.mk I)
  let unit (B : CochainComplex (ModuleCat.{max v u} R) ℤ) : B ⟶ GC.obj (FC.obj B) := {
    f := fun i => adj.unit.app (B.X i)
    comm' := fun i j _ => (adj.unit.naturality (B.d i j)) }
  have hGFA : ∀ i, (GC.obj (FC.obj A)).ExactAt i := by
    intro i
    rw [HomologicalComplex.exactAt_iff]
    exact ModuleCat.restrictScalars_map_exact (Ideal.Quotient.mk I) _
      ((HomologicalComplex.exactAt_iff _ i).1 (hFA i))
  have : QuasiIso (unit A) := quasiIso_of_exact _ hA hGFA
  have hepi (i : ℤ) : Epi ((unit A).f i) := reductionUnit_epi I _
  obtain ⟨g, hg⟩ := (CochainComplex.IsKProjective.exists_lift_of_quasiIso
    (unit A) (unit K ≫ GC.map f)).2 (fun _ => inferInstance) hepi
  refine ⟨g, ?_⟩
  ext i : 1
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_unit, adj.homEquiv_unit]
  exact (adj.unit.naturality (g.f i)).symm.trans
    (congrArg (fun h => h.f i) hg)

/-- The mapping cone of a quasi-isomorphism is acyclic. -/
private theorem exactAt_mappingCone_of_quasiIso
    {C : Type*} [Category C] [Abelian C]
    {X Y : CochainComplex C ℤ} (f : X ⟶ Y) [QuasiIso f] :
    ∀ i, (CochainComplex.mappingCone f).ExactAt i := by
  have hf : (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map f) := by
    rw [HomotopyCategory.quotient_map_mem_quasiIso_iff]
    exact (show QuasiIso f from inferInstance)
  rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic] at hf
  have h := ((HomotopyCategory.subcategoryAcyclic C).trW_iff_of_distinguished _
    (HomotopyCategory.mappingCone_triangleh_distinguished f)).1 hf
  exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_exactAt _).1 h

/-- A complex whose terms are each isomorphic to an object satisfying `P` is isomorphic to a
complex all of whose terms satisfy `P`. -/
private theorem exists_iso_with_terms
    {C : Type*} [Category C] [HasZeroMorphisms C]
    (P : C → Prop) (D : CochainComplex C ℤ)
    (hterms : ∀ i, ∃ M, P M ∧ Nonempty (M ≅ D.X i)) :
    ∃ B : CochainComplex C ℤ, (∀ i, P (B.X i)) ∧ Nonempty (B ≅ D) := by
  classical
  choose M hM e using hterms
  let e (i : ℤ) := (e i).some
  let B : CochainComplex C ℤ := {
    X := M
    d := fun i j => (e i).hom ≫ D.d i j ≫ (e j).inv
    shape := fun i j h => by rw [D.shape i j h]; simp
    d_comp_d' := fun i j k _ _ => by simp }
  exact ⟨B, hM, ⟨HomologicalComplex.Hom.isoOfComponents e (by intros; simp [B])⟩⟩

/-- If `f` is degreewise the inclusion of a summand, the cokernel of `f` is degreewise the
complementary summand. -/
private theorem exists_cokernel_term_iso
    {C : Type*} [Category C] [Abelian C]
    {K A : CochainComplex C ℤ} (f : K ⟶ A) (i : ℤ) (T : C)
    (a : K.X i ⊞ T ≅ A.X i) (ha : biprod.inl ≫ a.hom = f.f i) :
    Nonempty ((cokernel f).X i ≅ T) := by
  refine ⟨PreservesCokernel.iso (HomologicalComplex.eval C (ComplexShape.up ℤ) i) f ≪≫
    cokernel.mapIso (f.f i) biprod.inl (Iso.refl _) a.symm ?_ ≪≫ cokernelBiprodInlIso⟩
  simp [← ha]

/-- An acyclic complex is zero in the derived category. -/
private theorem isZero_derived_of_exact
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (A : CochainComplex C ℤ) (hA : ∀ i, A.ExactAt i) :
    IsZero (DerivedCategory.Q.obj A) := by
  have : QuasiIso (0 : (0 : CochainComplex C ℤ) ⟶ A) :=
    quasiIso_of_exact _ (fun i => HomologicalComplex.ExactAt.of_isZero (by
      exact (HomologicalComplex.eval C (ComplexShape.up ℤ) i).map_isZero (isZero_zero _))) hA
  exact (DerivedCategory.Q.map_isZero (isZero_zero _)).of_iso
    (asIso (DerivedCategory.Q.map (0 : (0 : CochainComplex C ℤ) ⟶ A))).symm

/-- The rotated cone short complex of `δ` is short exact. -/
private theorem shortExact_triangleRotateShortComplex
    {C : Type*} [Category C] [Abelian C] {X Y : CochainComplex C ℤ} (δ : X ⟶ Y) :
    (CochainComplex.mappingCone.triangleRotateShortComplex δ).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    (fun i => (CochainComplex.mappingCone.triangleRotateShortComplexSplitting δ i).shortExact)

/-- Identify the reduction of the cokernel of `f` with the shift of `E`, when the reduction of
the target of `f` is the mapping cone of `δ : E ⟶ ...` and `f` reduces to its inclusion. -/
private noncomputable def reductionCokernelIso
    {R : Type u} [CommRing R] (I : Ideal R)
    {K A : CochainComplex (ModuleCat.{max v u} R) ℤ}
    {E : CochainComplex (ModuleCat.{max v u} (R ⧸ I)) ℤ}
    (δ : E ⟶ ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K)
    (f : K ⟶ A)
    (e : ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj A ≅ CochainComplex.mappingCone δ)
    (he : ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map f ≫ e.hom = CochainComplex.mappingCone.inr δ) :
    ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (cokernel f) ≅ E⟦(1 : ℤ)⟧ := by
  let F := (ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
    (ComplexShape.up ℤ)
  let S := CochainComplex.mappingCone.triangleRotateShortComplex δ
  exact PreservesCokernel.iso F f ≪≫
    cokernel.mapIso (F.map f) S.f (Iso.refl _) e (he.trans (Category.id_comp _).symm) ≪≫
    (cokernelIsCokernel S.f).coconePointUniqueUpToIso
      (shortExact_triangleRotateShortComplex δ).gIsCokernel

/-- The identification `reductionCokernelIso` is compatible with the projection to the cokernel
and the connecting map of the rotated cone triangle. -/
private theorem reductionCokernelIso_π
    {R : Type u} [CommRing R] (I : Ideal R)
    {K A : CochainComplex (ModuleCat.{max v u} R) ℤ}
    {E : CochainComplex (ModuleCat.{max v u} (R ⧸ I)) ℤ}
    (δ : E ⟶ ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K)
    (f : K ⟶ A)
    (e : ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj A ≅ CochainComplex.mappingCone δ)
    (he : ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map f ≫ e.hom = CochainComplex.mappingCone.inr δ) :
    ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (cokernel.π f) ≫ (reductionCokernelIso I δ f e he).hom =
        e.hom ≫ (CochainComplex.mappingCone.triangle δ).mor₃ := by
  dsimp only [reductionCokernelIso, Iso.trans, cokernel.mapIso, Iso.refl, cokernel.map]
  simp only [Category.assoc, PreservesCokernel.π_iso_hom_assoc, cokernel.π_desc_assoc]
  congr 1
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (cokernelIsCokernel (CochainComplex.mappingCone.triangleRotateShortComplex δ).f)
    (shortExact_triangleRotateShortComplex δ).gIsCokernel WalkingParallelPair.one

set_option backward.isDefEq.respectTransparency false in
/-- The connecting map of the cone triangle of `f` agrees, up to homotopy and up to sign, with
the composite of the cokernel comparison and `δ⟦1⟧` after reduction. -/
private noncomputable def reductionCone_homotopy
    {R : Type u} [CommRing R] (I : Ideal R)
    {K A : CochainComplex (ModuleCat.{max v u} R) ℤ}
    {E : CochainComplex (ModuleCat.{max v u} (R ⧸ I)) ℤ}
    (δ : E ⟶ ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K)
    (f : K ⟶ A)
    (e : ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj A ≅ CochainComplex.mappingCone δ)
    (he : ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map f ≫ e.hom = CochainComplex.mappingCone.inr δ) :
    let FC := (ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
      (ComplexShape.up ℤ)
    Homotopy
      (FC.map (CochainComplex.mappingCone.triangle f).mor₃ ≫ (FC.commShiftIso 1).hom.app K)
      (-(FC.map (CochainComplex.mappingCone.descShortComplex
          (ShortComplex.cokernelSequence f)) ≫
        (reductionCokernelIso I δ f e he).hom ≫ δ⟦(1 : ℤ)⟧')) := by
  dsimp only
  let F := ModuleCat.extendScalars (Ideal.Quotient.mk I)
  let FC := F.mapHomologicalComplex (ComplexShape.up ℤ)
  have he' : FC.map f ≫ e.hom = 𝟙 _ ≫ CochainComplex.mappingCone.inr δ :=
    he.trans (Category.id_comp _).symm
  let ψ := CochainComplex.mappingCone.map (FC.map f) (CochainComplex.mappingCone.inr δ)
    (𝟙 _) e.hom he'
  let c := (CochainComplex.mappingCone.mapHomologicalComplexIso f F).hom ≫ ψ
  let r := CochainComplex.mappingCone.rotateHomotopyEquiv δ
  have hq : FC.map (CochainComplex.mappingCone.descShortComplex
        (ShortComplex.cokernelSequence f)) ≫ (reductionCokernelIso I δ f e he).hom =
      c ≫ r.inv := by
    rw [← CochainComplex.mappingCone.mapHomologicalComplexIso_hom_descShortComplex]
    dsimp [c]
    rw [Category.assoc, Category.assoc]
    congr 1
    change CochainComplex.mappingCone.desc (FC.map f) 0 (FC.map (cokernel.π f)) _ ≫
      (reductionCokernelIso I δ f e he).hom = ψ ≫ r.inv
    ext n : 1
    simp only [HomologicalComplex.comp_f]
    apply CochainComplex.mappingCone.ext_from _ (n + 1) n rfl
    · simp [ψ, r, CochainComplex.mappingCone.map,
        CochainComplex.mappingCone.rotateHomotopyEquiv]
    · simpa [ψ, r, CochainComplex.mappingCone.map,
        CochainComplex.mappingCone.rotateHomotopyEquiv, ← HomologicalComplex.comp_f] using
        congrArg (fun g => g.f n) (reductionCokernelIso_π I δ f e he)
  have ha : FC.map (CochainComplex.mappingCone.triangle f).mor₃ ≫
      (FC.commShiftIso 1).hom.app K =
        c ≫ (CochainComplex.mappingCone.triangle (CochainComplex.mappingCone.inr δ)).mor₃ := by
    rw [CochainComplex.mappingCone.map_δ]
    dsimp [c]
    rw [Category.assoc]
    congr 1
    symm
    have ht : (CochainComplex.mappingCone.triangle (FC.map f)).mor₃ ≫
        (𝟙 (FC.obj K))⟦(1 : ℤ)⟧' =
        ψ ≫ (CochainComplex.mappingCone.triangle (CochainComplex.mappingCone.inr δ)).mor₃ :=
      (CochainComplex.mappingCone.triangleMap (FC.map f)
        (CochainComplex.mappingCone.inr δ) (𝟙 _) e.hom he').comm₃
    erw [CategoryTheory.Functor.map_id, Category.comp_id] at ht
    exact ht.symm
  rw [ha, ← Category.assoc, hq]
  have H := r.homotopyInvHomId.compRight
    (CochainComplex.mappingCone.triangle (CochainComplex.mappingCone.inr δ)).mor₃
  have hr : r.hom ≫
      (CochainComplex.mappingCone.triangle (CochainComplex.mappingCone.inr δ)).mor₃ =
        -δ⟦(1 : ℤ)⟧' := CochainComplex.mappingCone.rotateHomotopyEquiv_comm₃ δ
  simpa only [Category.assoc, hr, Preadditive.comp_neg, Category.id_comp] using
    H.symm.compLeft c

set_option backward.isDefEq.respectTransparency false in
/-- Unshift the homotopy of `reductionCone_homotopy` into an equality in the derived category. -/
private theorem map_unshift_homotopy
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory D] (F : C ⥤ D) [F.Additive]
    {K A B : CochainComplex C ℤ} {E : CochainComplex D ℤ}
    (q : A ⟶ B) (a : A ⟶ K⟦(1 : ℤ)⟧)
    (e : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj B ≅ E⟦(1 : ℤ)⟧)
    (δ : E ⟶ (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
    (H : Homotopy
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map a ≫
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso 1).hom.app K)
      (-((F.mapHomologicalComplex (ComplexShape.up ℤ)).map q ≫ e.hom ≫ δ⟦(1 : ℤ)⟧'))) :
    let FC := F.mapHomologicalComplex (ComplexShape.up ℤ)
    let red := (FC.commShiftIso (-1)).app B ≪≫
      (shiftFunctor _ (-1 : ℤ)).mapIso e ≪≫
      (shiftFunctorCompIsoId _ (1 : ℤ) (-1) (by omega)).app E
    DerivedCategory.Q.map (FC.map (-(a⟦(-1 : ℤ)⟧' ≫
      (shiftFunctorCompIsoId _ (1 : ℤ) (-1) (by omega)).hom.app K))) =
      DerivedCategory.Q.map (FC.map (q⟦(-1 : ℤ)⟧')) ≫
        DerivedCategory.Q.map red.hom ≫ DerivedCategory.Q.map δ := by
  dsimp only
  let FC := F.mapHomologicalComplex (ComplexShape.up ℤ)
  let cK := (shiftFunctorCompIsoId _ (1 : ℤ) (-1) (by omega)).hom.app K
  let cE := (shiftFunctorCompIsoId _ (1 : ℤ) (-1) (by omega)).hom.app E
  let cFK := (shiftFunctorCompIsoId _ (1 : ℤ) (-1) (by omega)).hom.app (FC.obj K)
  have hl : (FC.commShiftIso (-1)).hom.app A ≫
      (FC.map a ≫ (FC.commShiftIso 1).hom.app K)⟦(-1 : ℤ)⟧' ≫ cFK =
        FC.map (a⟦(-1 : ℤ)⟧' ≫ cK) := by
    simp only [Functor.map_comp, Category.assoc]
    rw [← Functor.commShiftIso_hom_naturality_assoc]
    rw [Functor.map_shiftFunctorCompIsoId_hom_app]
  have hr : (FC.commShiftIso (-1)).hom.app A ≫
      (-(FC.map q ≫ e.hom ≫ δ⟦(1 : ℤ)⟧'))⟦(-1 : ℤ)⟧' ≫ cFK =
        -(FC.map (q⟦(-1 : ℤ)⟧') ≫ (FC.commShiftIso (-1)).hom.app B ≫
          e.hom⟦(-1 : ℤ)⟧' ≫ cE ≫ δ) := by
    simp only [Functor.map_neg, Functor.map_comp, Preadditive.comp_neg,
      Preadditive.neg_comp, Category.assoc]
    rw [← Functor.commShiftIso_hom_naturality_assoc]
    congr 1
    rw [show (δ⟦(1 : ℤ)⟧')⟦(-1 : ℤ)⟧' ≫ cFK = cE ≫ δ from
      (shiftFunctorCompIsoId _ (1 : ℤ) (-1) (by omega)).hom.naturality δ]
  have hh := DerivedCategory.Q_map_eq_of_homotopy D
    (((H.shift (-1)).compLeft ((FC.commShiftIso (-1)).hom.app A)).compRight cFK)
  simp only [Category.assoc] at hh
  rw [hl, hr] at hh
  simpa only [Functor.map_neg, Functor.map_comp, neg_neg, Iso.trans_hom,
    Functor.mapIso_hom, Iso.app_hom, Category.assoc] using congrArg Neg.neg hh

set_option backward.isDefEq.respectTransparency false in
/-- Lift a prescribed derived identification along with the reduced complex. The comparison
square commutes for the chosen complex isomorphism and the chosen derived representative. -/
theorem exists_boundedAbove_lift_representing_iso
    {R : Type u} [CommRing R] (I : Ideal R)
    (D : TotalDerivedExtensionScalars.{u, v, u} (Ideal.Quotient.mk I))
    (P : ModuleCat.{max v u} R → Prop)
    (K : DerivedCategory (ModuleCat.{max v u} R))
    (E : CochainComplex (ModuleCat.{max v u} (R ⧸ I)) ℤ)
    (hPprojective : ∀ M, P M → Module.Projective R M)
    (hPsum : ∀ M₁ M₂, (P M₁ ∧ P (M₁ ⊞ M₂)) ↔ (P M₁ ∧ P M₂))
    (hPsurjective : ∀ (M₁ M₂ : ModuleCat.{max v u} R) (f : M₁ ⟶ M₂),
      P M₁ → P M₂ →
      Function.Surjective
          (((ModuleCat.extendScalars.{u, u, max v u} (Ideal.Quotient.mk I)).map f).hom) →
        Function.Surjective f.hom)
    (hEbdd : ∃ b, E.IsStrictlyLE b)
    (hEterms : ∀ i, ∃ M, P M ∧ Nonempty
      (E.X i ≅
        (ModuleCat.extendScalars.{u, u, max v u} (Ideal.Quotient.mk I)).obj M))
    (eGiven : (DerivedCategory.Q).obj E ≅
      D.functor.obj K)
    (hKrep : ∃ KC : CochainComplex (ModuleCat.{max v u} R) ℤ,
      (∀ i, P (KC.X i)) ∧ (∃ b, KC.IsStrictlyLE b) ∧
        Nonempty ((DerivedCategory.Q).obj KC ≅ K)) :
    ∃ PC : CochainComplex (ModuleCat.{max v u} R) ℤ,
      (∀ i, P (PC.X i)) ∧
      (∃ b, PC.IsStrictlyLE b) ∧
      ∃ eRed :
        ((ModuleCat.extendScalars.{u, u, max v u} (Ideal.Quotient.mk I)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj PC ≅ E,
      ∃ eK : (DerivedCategory.Q).obj PC ≅ K,
        (D).comparison.app PC ≫
            DerivedCategory.Q.map eRed.hom ≫ eGiven.hom =
        (D).functor.map eK.hom := by
  classical
  let F := ModuleCat.extendScalars.{u, u, max v u} (Ideal.Quotient.mk I)
  let FC := F.mapHomologicalComplex (ComplexShape.up ℤ)
  obtain ⟨KC, hKC, ⟨bK, hbK⟩, ⟨eK⟩⟩ := hKrep
  have : KC.IsStrictlyLE bK := hbK
  have hproj : ∀ i : ℤ, Projective (KC.X i) := fun i => by
    have := hPprojective _ (hKC i)
    infer_instance
  have : KC.IsKProjective := CochainComplex.isKProjective_of_projective KC bK
  have : E.IsKProjective := isKProjective_of_reduction_terms I P E
    hPprojective hEbdd hEterms
  have hc : IsIso (D.comparison.app KC) := D.comparison_isIso_of_projective KC bK
  let e : DerivedCategory.Q.obj E ≅ DerivedCategory.Q.obj (FC.obj KC) :=
    eGiven ≪≫ D.functor.mapIso eK.symm ≪≫ @asIso _ _ _ _ (D.comparison.app KC) hc
  obtain ⟨δ, hδ, hδeq⟩ := exists_quasiIso_of_derived_iso E (FC.obj KC) e
  let C := CochainComplex.mappingCone δ
  have hCexact : ∀ i, C.ExactAt i := exactAt_mappingCone_of_quasiIso δ
  have hCbdd : ∃ b, C.IsStrictlyLE b := by
    obtain ⟨bE, hbE⟩ := hEbdd
    refine ⟨max bE bK, (CochainComplex.isStrictlyLE_iff _ _).2 ?_⟩
    intro i hi
    apply (CochainComplex.mappingCone.isZero_X_iff δ i).2
    exact ⟨E.isZero_of_isStrictlyLE bE _ (by omega),
      F.map_isZero (KC.isZero_of_isStrictlyLE bK i (by omega))⟩
  have hshiftTerms : ∀ i, ∃ M, P M ∧ Nonempty ((E⟦(1 : ℤ)⟧).X i ≅ F.obj M) := by
    intro i
    obtain ⟨M, hM, ⟨eM⟩⟩ := hEterms (i + 1)
    exact ⟨M, hM, ⟨E.shiftFunctorObjXIso 1 i (i + 1) rfl ≪≫ eM⟩⟩
  choose T hT ε using hshiftTerms
  let eT (i : ℤ) := (ε i).some
  let b (i : ℤ) :=
    (CochainComplex.mappingCone.triangleRotateShortComplexSplitting δ i).isoBinaryBiproduct
  have hsum (M N) (hM : P M) (hN : P N) : P (M ⊞ N) :=
    ((hPsum M N).2 ⟨hM, hN⟩).2
  have hCterms : ∀ i, ∃ M, P M ∧ Nonempty (C.X i ≅ F.obj M) := fun i =>
    ⟨KC.X i ⊞ T i, hsum _ _ (hKC i) (hT i),
      ⟨b i ≪≫ biprod.mapIso (Iso.refl _) (eT i) ≪≫ (F.mapBiprod _ _).symm⟩⟩
  obtain ⟨A, hA, ⟨bA, hbA⟩, hAexact, ⟨eA⟩⟩ :=
    LiftAcyclic.exists_lift_acyclic_complex I P hPprojective
      (fun M N hM hMN => ((hPsum M N).1 ⟨hM, hMN⟩).2)
      hPsurjective C hCbdd hCexact hCterms
  have : A.IsStrictlyLE bA := hbA
  have hFAexact : ∀ i, (FC.obj A).ExactAt i :=
    fun i => (hCexact i).of_iso eA.symm
  obtain ⟨f, hf⟩ := exists_complex_map_of_reduction I KC A hAexact hFAexact
    (CochainComplex.mappingCone.inr δ ≫ eA.inv)
  have hf' : FC.map f ≫ eA.hom = CochainComplex.mappingCone.inr δ := by rw [hf]; simp
  have ha : ∀ i, ∃ a : KC.X i ⊞ T i ≅ A.X i, biprod.inl ≫ a.hom = f.f i := by
    intro i
    let ei : F.obj (KC.X i) ⊞ F.obj (T i) ≅ F.obj (A.X i) :=
      biprod.mapIso (Iso.refl _) (eT i).symm ≪≫ (b i).symm ≪≫
        (HomologicalComplex.Hom.isoApp eA i).symm
    apply exists_biprod_iso_of_reduction I P hPprojective hsum hPsurjective
      (hKC i) (hA i) (hT i) (f.f i) ei
    have hfi := congrArg (fun g => g.f i) hf
    change F.map (f.f i) = _ at hfi
    rw [hfi]
    simp only [CochainComplex.shiftFunctor_obj_X', ShortComplex.map_X₂,
      HomologicalComplex.eval_obj, ShortComplex.map_X₁, ShortComplex.map_X₃,
      Functor.mapHomologicalComplex_obj_X, Iso.trans_hom, biprod.mapIso_hom,
      Iso.refl_hom, Iso.symm_hom, ShortComplex.Splitting.isoBinaryBiproduct_inv,
      ShortComplex.map_f, CochainComplex.mappingCone.triangleRotateShortComplex_f,
      Pretriangulated.Triangle.rotate_mor₁, CochainComplex.mappingCone.triangle_mor₂,
      HomologicalComplex.eval_map,
      CochainComplex.mappingCone.triangleRotateShortComplexSplitting_s,
      Int.reduceNeg, HomologicalComplex.Hom.isoApp_inv, biprod.inl_map_assoc,
      biprod.inl_desc_assoc, HomologicalComplex.comp_f, ei, b]
    exact Category.id_comp _
  choose a ha using ha
  have : Mono f := HomologicalComplex.mono_of_mono_f f (fun i => by
    rw [← ha i]
    infer_instance)
  let B := cokernel f
  have hBterms (i : ℤ) : Nonempty (B.X i ≅ T i) :=
    exists_cokernel_term_iso f i (T i) (a i) (ha i)
  have hBbdd : B.IsStrictlyLE bA := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact IsZero.of_epi ((cokernel.π f).f i) (A.isZero_of_isStrictlyLE bA i hi)
  have hBSbdd : (B⟦(-1 : ℤ)⟧).IsStrictlyLE (bA + 1) :=
    B.isStrictlyLE_shift bA (-1) (bA + 1) (by omega)
  obtain ⟨PC, hPC, ⟨ePC⟩⟩ := exists_iso_with_terms P (B⟦(-1 : ℤ)⟧) (fun i =>
    ⟨T (i + -1), hT _, ⟨((B.shiftFunctorObjXIso (-1) i (i + -1) rfl) ≪≫
      (hBterms (i + -1)).some).symm⟩⟩)
  let S := ShortComplex.cokernelSequence f
  have hS : S.ShortExact := {
    exact := ShortComplex.cokernelSequence_exact f
    mono_f := (show Mono f from inferInstance) }
  let q : CochainComplex.mappingCone f ⟶ B := CochainComplex.mappingCone.descShortComplex S
  let a : CochainComplex.mappingCone f ⟶ KC⟦(1 : ℤ)⟧ :=
    (CochainComplex.mappingCone.triangle f).mor₃
  have : QuasiIso q := CochainComplex.mappingCone.quasiIso_descShortComplex hS
  have ha : QuasiIso a := by
    have hzero := isZero_derived_of_exact A hAexact
    have : IsIso (DerivedCategory.triangleOfSESδ hS) :=
      ((DerivedCategory.triangleOfSES hS).isZero₂_iff_isIso₃
        (DerivedCategory.triangleOfSES_distinguished hS)).1 hzero
    have h : DerivedCategory.Q.map q ≫ DerivedCategory.triangleOfSESδ hS =
        DerivedCategory.Q.map a ≫ (DerivedCategory.Q.commShiftIso 1).hom.app KC :=
      DerivedCategory.descShortComplex_triangleOfSESδ hS
    have : IsIso (DerivedCategory.Q.map a ≫
        (DerivedCategory.Q.commShiftIso 1).hom.app KC) := by
      rw [← h]
      infer_instance
    have : IsIso (DerivedCategory.Q.map a) :=
      IsIso.of_isIso_comp_right _ ((DerivedCategory.Q.commShiftIso 1).hom.app KC)
    exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ a).1 this
  let q' := q⟦(-1 : ℤ)⟧'
  -- Rotation ends in -δ[1]; negate the connecting map to recover δ itself.
  let a' := -(a⟦(-1 : ℤ)⟧' ≫
    (shiftFunctorCompIsoId _ (1 : ℤ) (-1) (by omega)).hom.app KC)
  have : QuasiIso q' := inferInstance
  have : QuasiIso a' := by
    rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
    dsimp only [a']
    rw [Functor.map_neg]
    let g := DerivedCategory.Q.map (a⟦(-1 : ℤ)⟧' ≫
      (shiftFunctorCompIsoId _ (1 : ℤ) (-1) (by omega)).hom.app KC)
    have : IsIso g := inferInstance
    exact ⟨⟨-inv g, by simp [g], by simp [g]⟩⟩
  let eB := (asIso (DerivedCategory.Q.map q')).symm ≪≫
    asIso (DerivedCategory.Q.map a')
  let redB := (FC.commShiftIso (-1)).app B ≪≫
    (shiftFunctor _ (-1 : ℤ)).mapIso (reductionCokernelIso I δ f eA hf') ≪≫
    (shiftFunctorCompIsoId _ (1 : ℤ) (-1) (by omega)).app E
  have hn : DerivedCategory.Q.map (FC.map a') =
      DerivedCategory.Q.map (FC.map q') ≫ DerivedCategory.Q.map redB.hom ≫
        DerivedCategory.Q.map δ :=
    map_unshift_homotopy F q a (reductionCokernelIso I δ f eA hf') δ
      (reductionCone_homotopy I δ f eA hf')
  have hBcompat : D.comparison.app (B⟦(-1 : ℤ)⟧) ≫
      DerivedCategory.Q.map redB.hom ≫ DerivedCategory.Q.map δ =
        D.functor.map eB.hom ≫ D.comparison.app KC := by
    apply (cancel_epi (D.functor.map (DerivedCategory.Q.map q'))).1
    dsimp only [eB, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv]
    have hnat : D.functor.map (DerivedCategory.Q.map q') ≫
        D.comparison.app (B⟦(-1 : ℤ)⟧) =
          D.comparison.app ((CochainComplex.mappingCone f)⟦(-1 : ℤ)⟧) ≫
            DerivedCategory.Q.map (FC.map q') := D.comparison.naturality q'
    rw [← Category.assoc, ← Category.assoc, hnat]
    simp only [Category.assoc]
    rw [← hn]
    have hnat' : D.functor.map (DerivedCategory.Q.map a') ≫ D.comparison.app KC =
        D.comparison.app ((CochainComplex.mappingCone f)⟦(-1 : ℤ)⟧) ≫
          DerivedCategory.Q.map (FC.map a') := D.comparison.naturality a'
    rw [← hnat']
    simp [Category.assoc]
  let eRed := FC.mapIso ePC ≪≫ redB
  let eLift := DerivedCategory.Q.mapIso ePC ≪≫ eB ≪≫ eK
  refine ⟨PC, hPC, ⟨bA + 1, CochainComplex.isStrictlyLE_of_iso ePC.symm _⟩,
    eRed, eLift, ?_⟩
  change D.comparison.app PC ≫ DerivedCategory.Q.map eRed.hom ≫ eGiven.hom =
    D.functor.map eLift.hom
  apply (cancel_mono (D.functor.map eK.inv ≫ D.comparison.app KC)).1
  have heq : eGiven.hom ≫ D.functor.map eK.inv ≫ D.comparison.app KC =
      DerivedCategory.Q.map δ := by
    simpa only [e, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, asIso_hom] using hδeq.symm
  dsimp only [eRed, eLift, Iso.trans_hom, Functor.mapIso_hom]
  simp only [Functor.map_comp, Category.assoc]
  rw [heq]
  have hnat : D.functor.map (DerivedCategory.Q.map ePC.hom) ≫
      D.comparison.app (B⟦(-1 : ℤ)⟧) =
        D.comparison.app PC ≫ DerivedCategory.Q.map (FC.map ePC.hom) :=
    D.comparison.naturality ePC.hom
  rw [← Category.assoc, ← Category.assoc, ← hnat]
  simp only [Category.assoc]
  rw [hBcompat]
  simp

/-- The general form of [stacks 0BCA], for an arbitrary total derived extension-of-scalars datum
`D` along `R → R ⧸ I`: let `I ⊆ R` and let `P` be a class of projective `R`-modules, closed under
finite direct sums and complementary summands, such that surjectivity modulo `I` lifts to
surjectivity. A bounded above complex `E` of `R / I`-modules whose terms are reductions of
modules in `P`, and which represents `D.functor.obj K`, lifts to a bounded above complex with
terms in `P` representing `K`, provided `K` already has some such representative.

The source statement, for the canonical datum, is
`StacksDraft.Perfect.exists_boundedAbove_lift_representing`. -/
theorem exists_boundedAbove_lift_representing_of_datum
    {R : Type u} [CommRing R] (I : Ideal R)
    (D : TotalDerivedExtensionScalars.{u, v, u} (Ideal.Quotient.mk I))
    (P : ModuleCat.{max v u} R → Prop)
    (K : DerivedCategory (ModuleCat.{max v u} R))
    (E : CochainComplex (ModuleCat.{max v u} (R ⧸ I)) ℤ)
    (hPprojective : ∀ M, P M → Module.Projective R M)
    (hPsum : ∀ M₁ M₂, (P M₁ ∧ P (M₁ ⊞ M₂)) ↔ (P M₁ ∧ P M₂))
    (hPsurjective : ∀ (M₁ M₂ : ModuleCat.{max v u} R) (f : M₁ ⟶ M₂),
      P M₁ → P M₂ →
      Function.Surjective
          (((ModuleCat.extendScalars.{u, u, max v u} (Ideal.Quotient.mk I)).map f).hom) →
        Function.Surjective f.hom)
    (hEbdd : ∃ b, E.IsStrictlyLE b)
    (hEterms : ∀ i, ∃ M, P M ∧ Nonempty
      (E.X i ≅
        (ModuleCat.extendScalars.{u, u, max v u} (Ideal.Quotient.mk I)).obj M))
    (hErep : Nonempty
      ((DerivedCategory.Q).obj E ≅
        D.functor.obj K))
    (hKrep : ∃ KC : CochainComplex (ModuleCat.{max v u} R) ℤ,
      (∀ i, P (KC.X i)) ∧ (∃ b, KC.IsStrictlyLE b) ∧
        Nonempty ((DerivedCategory.Q).obj KC ≅ K)) :
    ∃ PC : CochainComplex (ModuleCat.{max v u} R) ℤ,
      (∀ i, P (PC.X i)) ∧
      (∃ b, PC.IsStrictlyLE b) ∧
      Nonempty
        (((ModuleCat.extendScalars.{u, u, max v u} (Ideal.Quotient.mk I)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj PC ≅ E) ∧
      Nonempty ((DerivedCategory.Q).obj PC ≅ K) := by
  obtain ⟨PC, hPC, hb, eRed, eK, _⟩ :=
    exists_boundedAbove_lift_representing_iso I D P K E hPprojective hPsum
      hPsurjective hEbdd hEterms hErep.some hKrep
  exact ⟨PC, hPC, hb, ⟨eRed⟩, ⟨eK⟩⟩

/-- **Stacks 0BCA.** Let `I ⊆ R` and let `P` be a class of projective `R`-modules, closed under
finite direct sums and complementary summands, such that surjectivity modulo `I` lifts to
surjectivity. A bounded above complex `E` of `R / I`-modules whose terms are reductions of
modules in `P`, and which represents `K ⊗ᴸ[R] R / I`, lifts to a bounded above complex with
terms in `P` representing `K`, provided `K` already has some such representative. -/
@[stacks 0BCA]
theorem exists_boundedAbove_lift_representing
    {R : Type u} [CommRing R] (I : Ideal R)
    (P : ModuleCat.{max v u} R → Prop)
    (K : DerivedCategory (ModuleCat.{max v u} R))
    (E : CochainComplex (ModuleCat.{max v u} (R ⧸ I)) ℤ)
    (hPprojective : ∀ M, P M → Module.Projective R M)
    (hPsum : ∀ M₁ M₂, (P M₁ ∧ P (M₁ ⊞ M₂)) ↔ (P M₁ ∧ P M₂))
    (hPsurjective : ∀ (M₁ M₂ : ModuleCat.{max v u} R) (f : M₁ ⟶ M₂),
      P M₁ → P M₂ →
      Function.Surjective
          (((ModuleCat.extendScalars.{u, u, max v u} (Ideal.Quotient.mk I)).map f).hom) →
        Function.Surjective f.hom)
    (hEbdd : ∃ b, E.IsStrictlyLE b)
    (hEterms : ∀ i, ∃ M, P M ∧ Nonempty
      (E.X i ≅
        (ModuleCat.extendScalars.{u, u, max v u} (Ideal.Quotient.mk I)).obj M))
    (hErep : Nonempty
      ((DerivedCategory.Q).obj E ≅
        (totalDerivedExtensionScalars.{u, u, v} (Ideal.Quotient.mk I)).functor.obj K))
    (hKrep : ∃ KC : CochainComplex (ModuleCat.{max v u} R) ℤ,
      (∀ i, P (KC.X i)) ∧ (∃ b, KC.IsStrictlyLE b) ∧
        Nonempty ((DerivedCategory.Q).obj KC ≅ K)) :
    ∃ PC : CochainComplex (ModuleCat.{max v u} R) ℤ,
      (∀ i, P (PC.X i)) ∧
      (∃ b, PC.IsStrictlyLE b) ∧
      Nonempty
        (((ModuleCat.extendScalars.{u, u, max v u} (Ideal.Quotient.mk I)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj PC ≅ E) ∧
      Nonempty ((DerivedCategory.Q).obj PC ≅ K) :=
  exists_boundedAbove_lift_representing_of_datum.{u, v} I
    (totalDerivedExtensionScalars.{u, u, v} (Ideal.Quotient.mk I)) P K E hPprojective hPsum
    hPsurjective hEbdd hEterms hErep hKrep

end BoundedAboveLift

/-! ### Reductions modulo an ideal in the Jacobson radical -/

section Jacobson

/-- The reduction of `f` modulo `I`, read through the identification of `M / IM` with the
extension of scalars of `M` along `R → R ⧸ I`. -/
private theorem inducedQuot_eq
    {R : Type u} [CommRing R] (I : Ideal R) {M N : ModuleCat.{max v u} R} (f : M ⟶ N) :
    inducedQuot I f.hom =
      (TensorProduct.quotTensorEquivQuotSMul (N : Type (max v u)) I).toLinearMap ∘ₗ
        ((f.hom.baseChange (R ⧸ I)).restrictScalars R) ∘ₗ
        (TensorProduct.quotTensorEquivQuotSMul (M : Type (max v u)) I).symm.toLinearMap := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  simp [inducedQuot]

/-- **Nakayama for a reduction.** If every element of `1 + I` is a unit and the target is a finite
module, a map whose extension of scalars along `R → R ⧸ I` is surjective is itself surjective.
This is condition (3) of [stacks 0BCA] for any class of finite modules. -/
theorem surjective_of_extendScalars_surjective
    {R : Type u} [CommRing R] (I : Ideal R) (hI : ∀ x ∈ I, IsUnit (1 + x))
    {M N : ModuleCat.{max v u} R} [Module.Finite R N] (f : M ⟶ N)
    (hf : Function.Surjective
      (((ModuleCat.extendScalars.{u, u, max v u} (Ideal.Quotient.mk I)).map f).hom)) :
    Function.Surjective f.hom := by
  refine surj_aux I hI f.hom ?_
  rw [inducedQuot_eq I f]
  refine (TensorProduct.quotTensorEquivQuotSMul (N : Type (max v u)) I).surjective.comp
    (Function.Surjective.comp (g := (f.hom.baseChange (R ⧸ I)).restrictScalars R) ?_
      (TensorProduct.quotTensorEquivQuotSMul (M : Type (max v u)) I).symm.surjective)
  exact hf

/-- The extension of scalars of `M` along `R → R ⧸ I`, viewed as an `R ⧸ I`-module, is `M / IM`. -/
noncomputable def extendScalarsQuotEquiv
    {R : Type u} [CommRing R] (I : Ideal R) (M : Type (max v u))
    [AddCommGroup M] [Module R M] :
    TensorProduct R (R ⧸ I) M ≃ₗ[R ⧸ I] (M ⧸ (I • (⊤ : Submodule R M))) :=
  (TensorProduct.quotTensorEquivQuotSMul M I).extendScalarsOfSurjective
    Ideal.Quotient.mk_surjective

end Jacobson

/-! ### Lifting a complex of finite stably free modules -/

section StablyFreeLift

/-- A complementary summand of a finite stably free module is stably free. This is the instance of
[stacks 0BC4] used to verify condition (2) of [stacks 0BCA] for the class of finite stably free
modules; the ambient module is finite, so both complements of the splitting are finite free. -/
private theorem isStablyFree_of_isStablyFree_prod
    {R : Type u} [CommRing R] (M₁ M₂ : Type (max v u))
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    [Module.Finite R M₁] [Module.IsStablyFree R M₁] [Module.IsStablyFree R (M₁ × M₂)] :
    Module.IsStablyFree R M₂ := by
  obtain ⟨A, _, _, _, _, _⟩ := Module.IsStablyFree.exist_free_prod R M₁
  obtain ⟨B, _, _, _, _, _⟩ := Module.IsStablyFree.exist_free_prod R (M₁ × M₂)
  have e₁ : ((M₂ × B) × M₁) ≃ₗ[R] ((M₁ × M₂) × B) :=
    (LinearEquiv.prodAssoc R M₂ B M₁).trans <|
      ((LinearEquiv.refl R M₂).prodCongr (LinearEquiv.prodComm R B M₁)).trans <|
        (LinearEquiv.prodAssoc R M₂ M₁ B).symm.trans
          ((LinearEquiv.prodComm R M₂ M₁).prodCongr (LinearEquiv.refl R B))
  have e : (M₂ × (B × (M₁ × A))) ≃ₗ[R] (((M₁ × M₂) × B) × A) :=
    (LinearEquiv.prodAssoc R M₂ B (M₁ × A)).symm.trans <|
      (LinearEquiv.prodAssoc R (M₂ × B) M₁ A).symm.trans
        (e₁.prodCongr (LinearEquiv.refl R A))
  have : Module.Free R (M₂ × (B × (M₁ × A))) := Module.Free.of_equiv e.symm
  exact Module.IsStablyFree.of_free_prod R M₂ (B × (M₁ × A))

/-- Condition (2) of [stacks 0BCA] for the class of finite stably free modules. -/
private theorem isStablyFree_biprod_iff
    {R : Type u} [CommRing R] (M₁ M₂ : ModuleCat.{max v u} R) :
    ((Module.Finite R M₁ ∧ Module.IsStablyFree R M₁) ∧
        (Module.Finite R (↑(M₁ ⊞ M₂) : Type (max v u)) ∧
          Module.IsStablyFree R (↑(M₁ ⊞ M₂) : Type (max v u)))) ↔
      ((Module.Finite R M₁ ∧ Module.IsStablyFree R M₁) ∧
        (Module.Finite R M₂ ∧ Module.IsStablyFree R M₂)) := by
  have e : (↑(M₁ ⊞ M₂) : Type (max v u)) ≃ₗ[R] (M₁ × M₂) :=
    (ModuleCat.biprodIsoProd M₁ M₂).toLinearEquiv
  constructor
  · rintro ⟨⟨h₁fin, h₁sf⟩, hfin, hsf⟩
    have : Module.Finite R (M₁ × M₂) := Module.Finite.equiv e
    have : Module.IsStablyFree R (M₁ × M₂) := hsf.equiv e
    exact ⟨⟨h₁fin, h₁sf⟩,
      Module.Finite.of_surjective (LinearMap.snd R M₁ M₂) LinearMap.snd_surjective,
      isStablyFree_of_isStablyFree_prod (M₁ : Type (max v u)) (M₂ : Type (max v u))⟩
  · rintro ⟨⟨h₁fin, h₁sf⟩, h₂fin, h₂sf⟩
    obtain ⟨A, _, _, _, _, _⟩ := Module.IsStablyFree.exist_free_prod R (M₁ : Type (max v u))
    obtain ⟨B, _, _, _, _, _⟩ := Module.IsStablyFree.exist_free_prod R (M₂ : Type (max v u))
    have : Module.Free R ((M₁ × M₂) × (A × B)) :=
      Module.Free.of_equiv (LinearEquiv.prodProdProdComm R M₁ M₂ A B).symm
    have : Module.IsStablyFree R (M₁ × M₂) :=
      Module.IsStablyFree.of_free_prod R _ (A × B)
    exact ⟨⟨h₁fin, h₁sf⟩, Module.Finite.equiv e.symm, this.equiv e.symm⟩

/-- Freeness of a lift is detected on its reduction: if `P` is finite projective, `E` is finite
free and `P / IP ≅ E`, then `P` is free. This is [stacks 0BC6] applied to a finite free module of
the same reduction. -/
theorem free_of_free_reduction
    {R : Type u} [CommRing R] (I : Ideal R) (hI : ∀ x ∈ I, IsUnit (1 + x))
    (P : Type (max v u)) [AddCommGroup P] [Module R P]
    [Module.Finite R P] [Module.Projective R P]
    (E : Type (max v u)) [AddCommGroup E] [Module (R ⧸ I) E]
    [Module.Finite (R ⧸ I) E] [Module.Free (R ⧸ I) E]
    (e : (P ⧸ (I • (⊤ : Submodule R P))) ≃ₗ[R ⧸ I] E) :
    Module.Free R P := by
  classical
  by_cases hq : Nontrivial (R ⧸ I)
  · have : Nontrivial (R ⧸ I) := hq
    -- A finite free `R`-module with the same reduction as `E`.
    let ι := Module.Free.ChooseBasisIndex (R ⧸ I) E
    have : Finite ι := Module.Finite.finite_basis (Module.Free.chooseBasis (R ⧸ I) E)
    let F := ι →₀ R
    have : Module.Finite R F :=
      Module.Finite.of_basis (Finsupp.basisSingleOne (R := R) (ι := ι))
    have : Module.Free R F := inferInstance
    have : Module.Projective R F := Module.Projective.of_free
    let eF : (F ⧸ (I • (⊤ : Submodule R F))) ≃ₗ[R ⧸ I] E :=
      (extendScalarsQuotEquiv.{u, v} I F).symm.trans <|
        (Algebra.TensorProduct.equivFinsuppOfBasis (R ⧸ I)
            (Finsupp.basisSingleOne (R := R) (ι := ι))).trans
          (Module.Free.chooseBasis (R ⧸ I) E).repr.symm
    obtain ⟨ePF⟩ := quot_iso_lift I hI (P := P) (P' := F)
      ⟨(e.trans eF.symm).restrictScalars R⟩
    exact Module.Free.of_equiv ePF.symm
  · -- `R ⧸ I` is trivial, hence `-1 ∈ I`, hence `0` is a unit and `R` is trivial.
    have hminus : (-1 : R) ∈ I := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      exact @Subsingleton.elim (R ⧸ I) (not_nontrivial_iff_subsingleton.mp hq) _ _
    have hzero : IsUnit (0 : R) := by simpa using hI (-1) hminus
    have : Subsingleton R := subsingleton_of_zero_eq_one (isUnit_zero_iff.mp hzero)
    exact Module.Free.of_subsingleton' R P

/-- Lift a prescribed derived identification along with a reduced complex of finite stably free
modules. This is the refinement of [stacks 0BCB] in which the comparison square commutes for the
chosen complex isomorphism and the chosen derived representative. -/
theorem exists_boundedAbove_isStablyFree_lift_representing_iso
    {R : Type u} [CommRing R] (I : Ideal R)
    (D : TotalDerivedExtensionScalars.{u, v, u} (Ideal.Quotient.mk I))
    (K : DerivedCategory (ModuleCat.{max v u} R))
    (E : CochainComplex (ModuleCat.{max v u} (R ⧸ I)) ℤ)
    (hEbdd : ∃ b, E.IsStrictlyLE b)
    (hEterms : ∀ i, Module.Finite (R ⧸ I) (E.X i) ∧ Module.IsStablyFree (R ⧸ I) (E.X i))
    (eGiven : (DerivedCategory.Q).obj E ≅ D.functor.obj K)
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K)
    (hI : ∀ x ∈ I, IsUnit (1 + x)) :
    ∃ P : CochainComplex (ModuleCat.{max v u} R) ℤ,
      (∀ i, Module.Finite R (P.X i) ∧ Module.IsStablyFree R (P.X i)) ∧
      (∃ b, P.IsStrictlyLE b) ∧
      ∃ eRed :
        ((ModuleCat.extendScalars.{u, u, max v u} (Ideal.Quotient.mk I)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P ≅ E,
      ∃ eK : (DerivedCategory.Q).obj P ≅ K,
        (D.comparison.app P ≫ DerivedCategory.Q.map eRed.hom ≫ eGiven.hom =
          D.functor.map eK.hom) ∧
        ∀ i, Module.Free (R ⧸ I) (E.X i) → Module.Free R (P.X i) := by
  classical
  let Pc : ModuleCat.{max v u} R → Prop :=
    fun M => Module.Finite R M ∧ Module.IsStablyFree R M
  obtain ⟨KC, hKC, hKCiso⟩ := hK
  have hKrep : ∃ KC : CochainComplex (ModuleCat.{max v u} R) ℤ,
      (∀ i, Pc (KC.X i)) ∧ (∃ b, KC.IsStrictlyLE b) ∧
        Nonempty ((DerivedCategory.Q).obj KC ≅ K) := by
    refine ⟨KC, fun i => ?_, hKC.upperBound, hKCiso⟩
    have : Module.Free R (KC.X i) := (hKC.finiteFree i).2
    exact ⟨(hKC.finiteFree i).1, inferInstance⟩
  obtain ⟨P, hP, hPbdd, eRed, eK, hcompat⟩ :=
    exists_boundedAbove_lift_representing_iso I D Pc K E
      (fun M hM => have := hM.2; inferInstance)
      (fun M₁ M₂ => isStablyFree_biprod_iff M₁ M₂)
      (fun _ N f _ hN hf => have := hN.1; surjective_of_extendScalars_surjective I hI f hf)
      hEbdd
      (fun i => by
        have := (hEterms i).1
        have := (hEterms i).2
        obtain ⟨M, hMfin, hMsf, ⟨e⟩⟩ :=
          exists_isStablyFree_lift.{u, max v u} I hI (E := (E.X i : Type (max v u)))
        exact ⟨M, ⟨hMfin, hMsf⟩,
          ⟨(e.symm.trans (extendScalarsQuotEquiv.{u, v} I (M : Type (max v u))).symm).toModuleIso⟩⟩)
      eGiven hKrep
  refine ⟨P, hP, hPbdd, eRed, eK, hcompat, fun i hEfree => ?_⟩
  have := (hP i).1
  have := (hP i).2
  have : Module.Projective R (P.X i) := inferInstance
  have := (hEterms i).1
  have : Module.Free (R ⧸ I) (E.X i) := hEfree
  refine free_of_free_reduction.{u, v} I hI (P.X i) (E.X i) ?_
  exact (extendScalarsQuotEquiv.{u, v} I (P.X i)).symm.trans
    ((HomologicalComplex.eval _ (ComplexShape.up ℤ) i).mapIso eRed).toLinearEquiv

/-- The general form of [stacks 0BCB], for an arbitrary total derived extension-of-scalars datum
`D` along `R → R ⧸ I`: let `I ⊆ R` be an ideal every element of whose coset `1 + I` is a unit. A
bounded above complex `E` of finite stably free `R ⧸ I`-modules representing `D.functor.obj K`,
for a pseudo-coherent object `K` of `D(R)`, lifts to a bounded above complex `P` of finite stably
free `R`-modules representing `K` with `P ⊗[R] R ⧸ I` isomorphic to `E`. Moreover `P` is free in
every degree in which `E` is free.

The source statement, for the canonical datum, is
`StacksDraft.Perfect.exists_boundedAbove_isStablyFree_lift_representing`. -/
theorem exists_boundedAbove_isStablyFree_lift_representing_of_datum
    {R : Type u} [CommRing R] (I : Ideal R)
    (D : TotalDerivedExtensionScalars.{u, v, u} (Ideal.Quotient.mk I))
    (K : DerivedCategory (ModuleCat.{max v u} R))
    (E : CochainComplex (ModuleCat.{max v u} (R ⧸ I)) ℤ)
    (hEbdd : ∃ b, E.IsStrictlyLE b)
    (hEterms : ∀ i, Module.Finite (R ⧸ I) (E.X i) ∧ Module.IsStablyFree (R ⧸ I) (E.X i))
    (hErep : Nonempty ((DerivedCategory.Q).obj E ≅ D.functor.obj K))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K)
    (hI : ∀ x ∈ I, IsUnit (1 + x)) :
    ∃ P : CochainComplex (ModuleCat.{max v u} R) ℤ,
      (∀ i, Module.Finite R (P.X i) ∧ Module.IsStablyFree R (P.X i)) ∧
      (∃ b, P.IsStrictlyLE b) ∧
      Nonempty
        (((ModuleCat.extendScalars.{u, u, max v u} (Ideal.Quotient.mk I)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P ≅ E) ∧
      Nonempty ((DerivedCategory.Q).obj P ≅ K) ∧
      (∀ i, Module.Free (R ⧸ I) (E.X i) → Module.Free R (P.X i)) := by
  obtain ⟨P, hP, hPbdd, eRed, eK, -, hfree⟩ :=
    exists_boundedAbove_isStablyFree_lift_representing_iso I D K E hEbdd hEterms
      hErep.some hK hI
  exact ⟨P, hP, hPbdd, ⟨eRed⟩, ⟨eK⟩, hfree⟩

/-- **Stacks 0BCB.** Let `I ⊆ R` be an ideal every element of whose coset `1 + I` is a unit. A
bounded above complex `E` of finite stably free `R ⧸ I`-modules representing `K ⊗ᴸ[R] R ⧸ I`, for
a pseudo-coherent object `K` of `D(R)`, lifts to a bounded above complex `P` of finite stably free
`R`-modules representing `K` with `P ⊗[R] R ⧸ I` isomorphic to `E`. Moreover `P` is free in every
degree in which `E` is free. -/
@[stacks 0BCB]
theorem exists_boundedAbove_isStablyFree_lift_representing
    {R : Type u} [CommRing R] (I : Ideal R)
    (K : DerivedCategory (ModuleCat.{max v u} R))
    (E : CochainComplex (ModuleCat.{max v u} (R ⧸ I)) ℤ)
    (hEbdd : ∃ b, E.IsStrictlyLE b)
    (hEterms : ∀ i, Module.Finite (R ⧸ I) (E.X i) ∧ Module.IsStablyFree (R ⧸ I) (E.X i))
    (hErep : Nonempty ((DerivedCategory.Q).obj E ≅
      (totalDerivedExtensionScalars.{u, u, v} (Ideal.Quotient.mk I)).functor.obj K))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K)
    (hI : ∀ x ∈ I, IsUnit (1 + x)) :
    ∃ P : CochainComplex (ModuleCat.{max v u} R) ℤ,
      (∀ i, Module.Finite R (P.X i) ∧ Module.IsStablyFree R (P.X i)) ∧
      (∃ b, P.IsStrictlyLE b) ∧
      Nonempty
        (((ModuleCat.extendScalars.{u, u, max v u} (Ideal.Quotient.mk I)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P ≅ E) ∧
      Nonempty ((DerivedCategory.Q).obj P ≅ K) ∧
      (∀ i, Module.Free (R ⧸ I) (E.X i) → Module.Free R (P.X i)) :=
  exists_boundedAbove_isStablyFree_lift_representing_of_datum.{u, v} I
    (totalDerivedExtensionScalars.{u, u, v} (Ideal.Quotient.mk I)) K E hEbdd hEterms hErep hK hI

end StablyFreeLift

end StacksDraft.Perfect
