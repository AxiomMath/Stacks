module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.Linear
public import Mathlib.Algebra.Homology.ShortComplex.Linear
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Finiteness.Ideal
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftUnit
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Extend.Finiteness
public import StacksFrontier.RingTheory.Module.LocallyFree.SheafBridge
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree

/-!
# Annihilating the cohomology of a finite locally free sheaf on an affine complement

Let `A` be a commutative ring, let `I` be a finitely generated ideal and let `U` be the open
complement of the closed subset `V(I)` of `Spec A`.  If some power of an ideal `J ⊆ I`
annihilates the degree `p` cohomology of the structure sheaf of `U`, then for every finite
locally free sheaf `F` on `U` some power of `J` annihilates the degree `p` cohomology of `F`.

Cohomology is the right derived functor of the global-sections functor
`SheafOfModules.evaluation U.ringCatSheaf (op ⊤)`, and the `A`-module structure on it comes
from the canonical ring map `A ⟶ Γ(U, 𝒪_U)`.

## Main results

* `AlgebraicGeometry.exists_pow_smul_derivedGlobalSections_eq_zero_of_isFiniteLocallyFree` is
  the annihilation statement.

## Implementation notes

The argument runs through the functor `H` sending an `A`-module `M` to the degree `p`
cohomology of the restriction of `M~` to `U`, viewed as an `A`-module.  That functor is
additive and `A`-linear on scalar endomorphisms, so it carries the annihilation hypothesis from
the free module of rank one to every finite free module.  A finite locally free sheaf on `U`
extends to a finitely presented `A`-module `M` whose localizations at suitable basic opens are
free, which upgrades the local annihilation to an annihilation of
`Module.annihilator A (H.obj M)` up to a power of `J`; finite generation of `I` converts that
into a single power.  Degree zero is separate: there the derived functor is the global-sections
functor itself, where the hypothesis already forces the scalar to vanish.

## References

* [Stacks Project, Tag 0BM5](https://stacks.math.columbia.edu/tag/0BM5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u v w

-- `Scheme.Modules` and its morphisms are definitions wrapping `SheafOfModules`, so instance
-- search for additivity and for the module structure on sections needs to see through them.
attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules
  AlgebraicGeometry.Scheme.Modules.Hom AlgebraicGeometry.Scheme.Modules.presheaf
  PresheafOfModules.presheaf ModuleCat.restrictScalars

namespace AlgebraicGeometry

section DerivedFunctorGenerics

variable {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]

/-- Taking injective resolutions is an additive functor to the homotopy category. -/
private lemma injectiveResolutions_additive : (injectiveResolutions C).Additive where
  map_add {X Y} f g := by
    have h : (HomotopyCategory.quotient C (ComplexShape.up ℕ)).map
          (InjectiveResolution.desc (f + g) (injectiveResolution Y) (injectiveResolution X)) =
        (HomotopyCategory.quotient C (ComplexShape.up ℕ)).map
          (InjectiveResolution.desc f (injectiveResolution Y) (injectiveResolution X) +
            InjectiveResolution.desc g (injectiveResolution Y) (injectiveResolution X)) := by
      apply HomotopyCategory.eq_of_homotopy
      apply InjectiveResolution.descHomotopy (f + g) <;>
        simp [Preadditive.comp_add, Preadditive.add_comp]
    exact h.trans ((HomotopyCategory.quotient C (ComplexShape.up ℕ)).map_add)

/-- The right derived functors of an additive functor are additive. -/
private lemma rightDerived_additive {D : Type*} [Category.{w} D] [Abelian D]
    (G : C ⥤ D) [G.Additive] (p : ℕ) : (G.rightDerived p).Additive := by
  have := injectiveResolutions_additive (C := C)
  dsimp [Functor.rightDerived, Functor.rightDerivedToHomotopyCategory]
  infer_instance

/-- If an endomorphism of the identity functor acts on an additive functor `G` to modules as
multiplication by a scalar `r`, then it acts the same way on every right derived functor of
`G`. -/
private lemma rightDerived_map_central {R : Type w} [CommRing R] (G : C ⥤ ModuleCat.{w} R)
    [G.Additive] (η : 𝟭 C ⟶ 𝟭 C) (r : R)
    (hη : ∀ Y, G.map (η.app Y) = r • 𝟙 (G.obj Y)) (p : ℕ) (Y : C) :
    (G.rightDerived p).map (η.app Y) = r • 𝟙 _ := by
  let P := injectiveResolution Y
  let K := (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj P.cocomplex
  let Z : ModuleCat.{w} R :=
    (HomologicalComplex.homologyFunctor (ModuleCat.{w} R) (ComplexShape.up ℕ) p).obj K
  let e : (G.rightDerived p).obj Y ≅ Z := P.isoRightDerivedObj G p
  let φ : P.cocomplex ⟶ P.cocomplex :=
    { f := fun i => η.app (P.cocomplex.X i)
      comm' := fun i j _ => (η.naturality (P.cocomplex.d i j)).symm }
  have h := P.isoRightDerivedObj_hom_naturality (η.app Y) P φ (η.naturality (P.ι.f 0)) G p
  have hφ : (G.mapHomologicalComplex (ComplexShape.up ℕ)).map φ = r • 𝟙 K :=
    HomologicalComplex.Hom.ext (funext fun _ => hη _)
  have hh : (HomologicalComplex.homologyMap (r • 𝟙 K) p : Z ⟶ Z) = r • 𝟙 Z := by
    show ShortComplex.homologyMap (r • 𝟙 (K.sc p)) = _
    rw [ShortComplex.homologyMap_smul, ShortComplex.homologyMap_id]
    rfl
  simp only [Functor.comp_map, hφ] at h
  change (G.rightDerived p).map (η.app Y) ≫ e.hom =
      e.hom ≫ (HomologicalComplex.homologyMap (r • 𝟙 K) p : Z ⟶ Z) at h
  rw [hh] at h
  exact (cancel_mono e.hom).mp
    (h.trans (ModuleCat.hom_ext (LinearMap.ext fun x => (map_smul e.hom.hom r x).symm)))

end DerivedFunctorGenerics

section ScalarAction

/-- Multiplication by a section of the structure sheaf, as a linear endomorphism of the sections
of an `𝒪ₓ`-module.  Pinning this as a definition keeps every later statement about it at the
`Γ(M, U)` spelling, where the module structure is the one Mathlib declares. -/
private def scalarSection {X : Scheme.{u}} (M : X.Modules) {U : X.Opens} (s : Γ(X, U)) :
    Γ(M, U) →ₗ[Γ(X, U)] Γ(M, U) where
  toFun x := s • x
  map_add' _ _ := smul_add _ _ _
  map_smul' a x := smul_comm _ a x

private def scalarSheafNatTrans (X : Scheme.{u}) (r : Γ(X, ⊤)) : 𝟭 X.Modules ⟶ 𝟭 X.Modules where
  app M := show M ⟶ M from
    { val :=
        { app := fun ⟨U⟩ =>
            ModuleCat.ofHom (scalarSection M (X.presheaf.map (homOfLE (le_top (a := U))).op r))
          naturality := by
            rintro ⟨U⟩ ⟨V⟩ i
            refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
            have hr := ConcreteCategory.congr_hom
              (X.presheaf.map_comp (homOfLE (le_top (a := U))).op i) r
            have hms := M.map_smul i.unop (X.presheaf.map (homOfLE (le_top (a := U))).op r) x
            exact (hms.trans
              (congrArg (fun t : Γ(X, V) => t • M.presheaf.map i x) hr.symm)).symm } }
  naturality {M N} f := by
    apply SheafOfModules.hom_ext
    ext U x
    exact ((f.val.app U).hom.map_smul _ _).symm

/-- On cohomology, multiplication by the image of `a : A` acts as multiplication by `a`. -/
private lemma rightDerived_map_scalarSheafMap (X : Scheme.{u}) (A : Type u) [CommRing A]
    (c : A →+* Γ(X, ⊤)) (a : A) (p : ℕ) (M : X.Modules) :
    (ModuleCat.restrictScalars c).map
      (((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).rightDerived p).map
        ((scalarSheafNatTrans X (c a)).app M)) =
      a • 𝟙 ((ModuleCat.restrictScalars c).obj
        (((SheafOfModules.evaluation X.ringCatSheaf
          (op (⊤ : X.Opens))).rightDerived p).obj M)) := by
  let _ : CommRing ↑(X.ringCatSheaf.obj.obj (op (⊤ : X.Opens))) :=
    inferInstanceAs (CommRing ↑Γ(X, ⊤))
  let G := SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))
  let r₀ : ↑(X.ringCatSheaf.obj.obj (op (⊤ : X.Opens))) := c a
  have hcentral : ∀ N : X.Modules,
      G.map ((scalarSheafNatTrans X (c a)).app N) = r₀ • 𝟙 (G.obj N) := by
    intro N
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    have hid : scalarSection N
        (X.presheaf.map (homOfLE (le_top (a := (⊤ : X.Opens)))).op (c a)) x = r₀ • x := by
      rw [show (homOfLE (le_top (a := (⊤ : X.Opens)))).op = 𝟙 _ from Subsingleton.elim _ _,
        X.presheaf.map_id]
      rfl
    exact hid
  have h := rightDerived_map_central G (scalarSheafNatTrans X (c a)) r₀ hcentral p M
  show (ModuleCat.restrictScalars c).map ((G.rightDerived p).map _) = _
  rw [h]
  rfl

/-- In degree zero the hypothesis forces the scalar itself to vanish in `Γ(X, 𝒪_X)`, so it
annihilates the global sections of every sheaf of modules. -/
private lemma annihilates_sections_of_annihilates_unit (X : Scheme.{u}) (A : Type u) [CommRing A]
    (c : A →+* Γ(X, ⊤)) (a : A)
    (h : ∀ x : (ModuleCat.restrictScalars c).obj
        (((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).rightDerived 0).obj
          (SheafOfModules.unit X.ringCatSheaf)), a • x = 0)
    (F : X.Modules)
    (x : (ModuleCat.restrictScalars c).obj
        (((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).rightDerived 0).obj F)) :
    a • x = 0 := by
  let G := SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))
  have : PreservesFiniteLimits G :=
    _root_.SheafOfModules.Finite.evaluationPreservesFiniteLimits _ _
  let e := G.rightDerivedZeroIsoSelf
  let eA := (ModuleCat.restrictScalars c).mapIso (e.app (SheafOfModules.unit X.ringCatSheaf))
  have ha : c a = 0 := by
    have hh := congrArg (DFunLike.coe (ModuleCat.Hom.hom eA.hom)) (h (eA.inv (1 : Γ(X, ⊤))))
    have he : (ModuleCat.Hom.hom eA.hom) (eA.inv (1 : Γ(X, ⊤))) = (1 : Γ(X, ⊤)) :=
      ConcreteCategory.congr_hom eA.inv_hom_id (1 : Γ(X, ⊤))
    rw [map_smul, map_zero, he] at hh
    change c a * 1 = 0 at hh
    simpa using hh
  have h0 : ∀ y : (((SheafOfModules.evaluation X.ringCatSheaf
      (op (⊤ : X.Opens))).rightDerived 0).obj F),
      (0 : ↑(X.ringCatSheaf.obj.obj (op (⊤ : X.Opens)))) • y = 0 :=
    fun y => zero_smul _ y
  refine (ModuleCat.restrictScalars.smul_def c a x).trans ?_
  rw [ha]
  exact h0 _

end ScalarAction

section Annihilation

/-- Multiplication by `a` on `M~` is the scalar endomorphism attached to the image of `a` in
`Γ(Spec A, 𝒪)`. -/
private lemma tilde_map_smul_id (A : Type u) [CommRing A] (M : ModuleCat.{u} A) (a : A) :
    (tilde.functor (.of A)).map (a • 𝟙 M) =
      (scalarSheafNatTrans (Spec (.of A)) ((Scheme.ΓSpecIso (.of A)).inv a)).app (tilde M) := by
  ext U x
  apply Subtype.ext
  funext y
  show (LocalizedModule.map y.1.asIdeal.primeCompl (a • LinearMap.id)) (x.val y) = _
  rw [map_smul, LocalizedModule.map_id]
  show a • x.val y = algebraMap A (Localization.AtPrime y.val.asIdeal) a • x.val y
  exact (IsScalarTower.algebraMap_smul (Localization.AtPrime y.val.asIdeal) a (x.val y)).symm

/-- Restricting a scalar endomorphism along an open immersion gives the scalar endomorphism
attached to the restricted section. -/
private lemma restrict_scalarSheafNatTrans {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (r : Γ(Y, ⊤)) (M : Y.Modules) :
    (Scheme.Modules.restrictFunctor f).map ((scalarSheafNatTrans Y r).app M) =
      (scalarSheafNatTrans X (f.appTop r)).app (M.restrict f) := by
  ext U x
  let z : Γ(M, f ''ᵁ U) := (M.restrictAppIso f U).hom x
  show (Y.presheaf.map (homOfLE (show f ''ᵁ U ≤ ⊤ from le_top)).op r) • z =
    (f.appIso U).inv (X.presheaf.map U.leTop.op (f.appTop r)) • z
  congr 1
  have h : f.appTop ≫ X.presheaf.map U.leTop.op ≫ (f.appIso U).inv =
      Y.presheaf.map (f ''ᵁ U).leTop.op := by
    rw [← Category.assoc, Iso.comp_inv_eq]
    simp only [Scheme.Hom.appTop, Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE]
    rfl
  exact (ConcreteCategory.congr_hom h r).symm

/-- A surjection onto a finitely presented module which becomes projective after localization
splits after multiplying by an element of the localizing submonoid. -/
private lemma exists_smul_factorization_of_localized_projective {R : Type u} [CommRing R]
    {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.FinitePresentation R M] (S : Submonoid R) (q : N →ₗ[R] M)
    (hq : Function.Surjective q)
    [Module.Projective (Localization S) (LocalizedModule S M)] :
    ∃ (a : S) (g : M →ₗ[R] N), q.comp g = (a : R) • LinearMap.id := by
  obtain ⟨g, hg⟩ := Module.projective_lifting_property
    (LocalizedModule.map S q) LinearMap.id (LocalizedModule.map_surjective _ _ hq)
  obtain ⟨⟨g₀, s⟩, hs⟩ := IsLocalizedModule.mk'_surjective S (LocalizedModule.map S) g
  have hsg : s • g = LocalizedModule.map S g₀ := by
    rw [← hs]
    exact IsLocalizedModule.mk'_cancel' _ _ _
  have heq : LocalizedModule.map S (q.comp g₀) =
      LocalizedModule.map S ((s : R) • LinearMap.id) := by
    rw [map_smul, LocalizedModule.map_id]
    have hcomp : LocalizedModule.map S (q.comp g₀) =
        (LocalizedModule.map S q).comp (LocalizedModule.map S g₀) := by
      apply LinearMap.restrictScalars_injective R
      apply IsLocalizedModule.ext S (LocalizedModule.mkLinearMap S M)
      · exact IsLocalizedModule.map_units (LocalizedModule.mkLinearMap S M)
      ext x
      simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply,
        LocalizedModule.mkLinearMap_apply, LocalizedModule.map_mk]
    rw [hcomp, ← hsg]
    show (LocalizedModule.map S q).comp ((s : R) • g) = _
    rw [LinearMap.comp_smul, hg]
  obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_iff_exists S (LocalizedModule.map S)).mp heq
  refine ⟨t * s, (t : R) • g₀, ?_⟩
  rw [LinearMap.comp_smul]
  simpa only [Submonoid.smul_def, smul_smul, Submonoid.coe_mul] using ht

/-- If `a` kills every element of `Y` and `X ≅ Y`, then `a` kills every element of `X`. -/
private lemma smul_eq_zero_of_iso {R : Type u} [CommRing R] {X Y : ModuleCat.{u} R} (i : X ≅ Y)
    (a : R) (h : ∀ y : Y, a • y = 0) (x : X) : a • x = 0 :=
  (ModuleCat.mono_iff_injective i.hom).mp inferInstance (by rw [map_smul, map_zero]; exact h _)

/-- An additive functor carries an annihilator of its value on the free module of rank one to
an annihilator of its value on every finite free module. -/
private lemma annihilates_functor_obj_of_finite_free {R : Type u} [CommRing R]
    (H : ModuleCat.{u} R ⥤ ModuleCat.{u} R) [H.Additive] (a : R)
    (ha : ∀ x : H.obj (ModuleCat.of R R), a • x = 0) (N : ModuleCat.{u} R) [Module.Free R N]
    [Module.Finite R N] : ∀ x : H.obj N, a • x = 0 := by
  classical
  let b := Module.Free.chooseBasis R N
  let _ : Fintype (Module.Free.ChooseBasisIndex R N) := Fintype.ofFinite _
  let π (i : Module.Free.ChooseBasisIndex R N) : N ⟶ ModuleCat.of R R :=
    ModuleCat.ofHom (b.coord i)
  let ι (i : Module.Free.ChooseBasisIndex R N) : ModuleCat.of R R ⟶ N :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton R N (b i))
  have hid : ∑ i, π i ≫ ι i = 𝟙 N := by
    ext x
    simp [π, ι]
  have hH : ∑ i, H.map (π i) ≫ H.map (ι i) = 𝟙 (H.obj N) := by
    simpa using congrArg (fun f : N ⟶ N => H.map f) hid
  intro x
  have hx : (∑ i, H.map (ι i) (H.map (π i) x)) = x := by
    simpa using ConcreteCategory.congr_hom hH x
  rw [← hx, Finset.smul_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [← map_smul, ha, map_zero]

/-- A local annihilation statement over the complement of `V(I)`, for `I` finitely generated,
upgrades to a single power of `J`. -/
private lemma exists_pow_le_of_local_annihilation {R : Type u} [CommRing R] (I J K : Ideal R)
    (hI : I.FG) (hJI : J ≤ I) (n : ℕ)
    (hlocal : ∀ p : PrimeSpectrum R, ¬ I ≤ p.asIdeal →
      ∃ a ∉ p.asIdeal, ∀ b ∈ J ^ n, a * b ∈ K) :
    ∃ m : ℕ, J ^ m ≤ K := by
  let L := K.colon ((J ^ n : Ideal R) : Set R)
  have hrad : I ≤ L.radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf fun P hP => ?_
    by_contra hIP
    obtain ⟨a, ha, h⟩ := hlocal ⟨P, hP.2⟩ hIP
    exact ha (hP.1 (show a ∈ L from (Submodule.mem_colon.mpr h)))
  obtain ⟨m, hm⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad hI
  refine ⟨m + n, ?_⟩
  rw [pow_add]
  exact Ideal.mul_le.mpr fun a ha b hb =>
    Submodule.mem_colon.mp (hm (pow_le_pow_left' hJI m ha)) b hb

/-- The abstract heart of the argument: an additive functor on modules which is linear on
scalar endomorphisms, annihilated on the free module of rank one by `J ^ n`, is annihilated on
any finitely presented module with locally projective localizations by some power of `J`. -/
private lemma exists_pow_annihilates_linear_functor_obj {R : Type u} [CommRing R]
    (H : ModuleCat.{u} R ⥤ ModuleCat.{u} R) [H.Additive]
    (hH : ∀ (M : ModuleCat.{u} R) (r : R), H.map (r • 𝟙 M) = r • 𝟙 (H.obj M))
    (I J : Ideal R) (hI : I.FG) (hJI : J ≤ I) (n : ℕ)
    (hn : ∀ a ∈ J ^ n, ∀ x : H.obj (ModuleCat.of R R), a • x = 0)
    (M : ModuleCat.{u} R) [Module.FinitePresentation R M]
    (hM : ∀ p : PrimeSpectrum R, ¬ I ≤ p.asIdeal →
      ∃ S : Submonoid R, S ≤ p.asIdeal.primeCompl ∧
        Module.Projective (Localization S) (LocalizedModule S M)) :
    ∃ m : ℕ, ∀ a ∈ J ^ m, ∀ x : H.obj M, a • x = 0 := by
  classical
  obtain ⟨k, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := M)
  let N := ModuleCat.of R (Fin k →₀ R)
  let q : N →ₗ[R] M := Finsupp.linearCombination R s
  have hq : Function.Surjective q := by
    rwa [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
  obtain ⟨m, hm⟩ := exists_pow_le_of_local_annihilation I J
    (Module.annihilator R (H.obj M)) hI hJI n (fun p hp => by
      obtain ⟨S, hS, hMS⟩ := hM p hp
      obtain ⟨a, g, hg⟩ := exists_smul_factorization_of_localized_projective S q hq
      refine ⟨a, hS a.property, fun b hb => ?_⟩
      refine Module.mem_annihilator.mpr fun x => ?_
      have heq : H.map (ModuleCat.ofHom g) ≫ H.map (ModuleCat.ofHom q) = a.val • 𝟙 (H.obj M) := by
        rw [← H.map_comp]
        show H.map (ModuleCat.ofHom (q.comp g)) = _
        rw [hg]
        exact hH M a.val
      have hx : H.map (ModuleCat.ofHom q) (H.map (ModuleCat.ofHom g) x) = a.val • x :=
        ConcreteCategory.congr_hom heq x
      rw [mul_comm, mul_smul, ← hx, ← map_smul,
        annihilates_functor_obj_of_finite_free H b (hn b hb) N, map_zero])
  exact ⟨m, fun a ha x => Module.mem_annihilator.mp (hm ha) x⟩

end Annihilation

section Extension

/-- A locally free sheaf is free on some neighbourhood of any given point. -/
private lemma exists_restrict_iso_free {X : Scheme.{u}} (F : X.Modules)
    [SheafOfModules.IsLocallyFree.{u, u, u} F] (x : X) :
    ∃ (V : X.Opens) (_ : x ∈ V) (κ : Type u),
      Nonempty (F.restrict V.ι ≅ SheafOfModules.free.{u} κ) := by
  obtain ⟨q, hq⟩ := SheafOfModules.IsLocallyFree.exists_isLocallyFreeData (M := F)
  have hcover := q.coversTop
  rw [Opens.coversTop_iff, IsOpenCover] at hcover
  have hx : x ∈ ⨆ i, q.X i := by
    rw [hcover]
    trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  let V := q.X i
  let E := (Scheme.Modules.overEquiv V).functor
  have : IsIso (q.generators i).π := hq.isIso i
  have hpres : PreservesColimitsOfShape.{u, u} (Discrete (q.generators i).I) E :=
    Functor.instPreservesColimitsOfShapeOfIsLeftAdjoint.{u, u, u, u + 1, u, u + 1} E
  exact ⟨V, hi, (q.generators i).I, ⟨((Scheme.Modules.overFunctorEquiv V).app F).symm ≪≫
    E.mapIso (asIso (q.generators i).π).symm ≪≫
    (@SheafOfModules.mapFreeIso _ _ _ _ _ _ _ _ _ _ _ _ E (q.generators i).I hpres
      (Iso.refl _)).symm⟩⟩

/-- If `M~` restricted to `U` is locally free, then `M` is free after localizing at a suitable
basic open neighbourhood of any point of `U`. -/
private lemma exists_basicOpen_localized_free (A : Type u) [CommRing A] (M : ModuleCat.{u} A)
    (U : (Spec (.of A)).Opens) (F : (U : Scheme).Modules)
    [SheafOfModules.IsLocallyFree.{u, u, u} F] (e : F ≅ (tilde M).restrict U.ι)
    (q : PrimeSpectrum A) (hq : q ∈ U) :
    ∃ f ∉ q.asIdeal,
      Module.Free (Localization.Away f) (LocalizedModule (Submonoid.powers f) M) := by
  obtain ⟨V, hxV, κ, ⟨eV⟩⟩ := exists_restrict_iso_free F (⟨q, hq⟩ : U)
  have hqW : q ∈ U.ι ''ᵁ V := ⟨⟨q, hq⟩, hxV, rfl⟩
  obtain ⟨B, ⟨f, rfl⟩, hqf, hfW⟩ :=
    Opens.isBasis_iff_nbhd.mp (PrimeSpectrum.isBasis_basic_opens (R := A)) hqW
  refine ⟨f, hqf, (tilde_restrict_basicOpen_free_iff A M f).mp ⟨κ, ⟨?_⟩⟩⟩
  let g := V.ι ≫ U.ι
  have hrange : Set.range (specBasicOpen A f).ι ⊆ Set.range g := by
    show Set.range (specBasicOpen A f).ι ⊆ Set.range (U.ι ∘ V.ι)
    rwa [Set.range_comp, Scheme.Opens.range_ι, Scheme.Opens.range_ι]
  let j := IsOpenImmersion.lift g (specBasicOpen A f).ι hrange
  have hj : j ≫ g = (specBasicOpen A f).ι := IsOpenImmersion.lift_fac _ _ _
  let e₁ : (tilde M).restrict g ≅ SheafOfModules.free.{u} κ :=
    (Scheme.Modules.restrictFunctorComp V.ι U.ι).app (tilde M) ≪≫
      (Scheme.Modules.restrictFunctor V.ι).mapIso e.symm ≪≫ eV
  exact (Scheme.Modules.restrictFunctorCongr hj.symm).app (tilde M) ≪≫
    (Scheme.Modules.restrictFunctorComp j g).app (tilde M) ≪≫
    (Scheme.Modules.restrictFunctor j).mapIso e₁ ≪≫ restrictFunctor_obj_free_iso j κ

/-- A finite locally free sheaf of modules is of finite presentation. -/
private lemma isFinitePresentation_of_isFiniteLocallyFree {X : Scheme.{u}} (F : X.Modules)
    [h : SheafOfModules.IsFiniteLocallyFree.{u, u, u} F] : F.IsFinitePresentation := by
  have h' : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} F :=
    { exists_isFiniteLocallyFreeData := h.exists_isFiniteLocallyFreeData }
  exact Stacks.FiniteLocallyFree.isFinitePresentation F

/-- A finitely presented sheaf of modules on the complement of `V(I)` in `Spec A` is the
restriction of `M~` for a finitely presented `A`-module `M`. -/
private lemma exists_finitePresentation_extension (A : Type u) [CommRing A] (I : Ideal A)
    (hI : I.FG) (U : (Spec (.of A)).Opens)
    (hU : (U : Set (Spec (.of A))) = (PrimeSpectrum.zeroLocus (I : Set A))ᶜ)
    (F : (U : Scheme).Modules) [F.IsFinitePresentation] :
    ∃ M : ModuleCat.{u} A, Module.FinitePresentation A M ∧
      Nonempty (F ≅ ((tilde.functor (CommRingCat.of A)).obj M).restrict U.ι) := by
  have hUcompact : IsCompact (U : Set (Spec (.of A))) := by
    rw [hU]
    exact (PrimeSpectrum.isRetrocompact_zeroLocus_compl_of_fg hI).isCompact
  obtain ⟨G, hGfp, ⟨eGF⟩⟩ := exists_extension_of_isFinitePresentation U hUcompact F
  let M : ModuleCat.{u} A := (moduleSpecΓFunctor (R := CommRingCat.of A)).obj G
  have : G.IsQuasicoherent := SheafOfModules.instIsQuasicoherentOfIsFinitePresentation G
  have hGiso : IsIso (Scheme.Modules.fromTildeΓ (R := CommRingCat.of A) G) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := CommRingCat.of A) G
  let e : (tilde.functor (CommRingCat.of A)).obj M ≅ G :=
    @CategoryTheory.asIso _ _ _ _ (Scheme.Modules.fromTildeΓ (R := CommRingCat.of A) G) hGiso
  have htilde : ((tilde.functor (CommRingCat.of A)).obj M).IsFinitePresentation :=
    (SheafOfModules.isFinitePresentation (Spec (CommRingCat.of A)).ringCatSheaf).prop_of_iso
      e.symm hGfp
  exact ⟨M, (tilde_isFinitePresentation_iff (R := CommRingCat.of A) M).mp htilde,
    ⟨((Scheme.Modules.restrictFunctor U.ι).mapIso e ≪≫ eGF).symm⟩⟩

/-- Taking `M ↦ M~` is an additive functor. -/
private lemma tilde_functor_additive (A : Type u) [CommRing A] :
    (tilde.functor (.of A)).Additive := by
  have : (tilde.functor (.of A)).IsLeftAdjoint := tilde.adjunction.isLeftAdjoint
  have : (tilde.functor (.of A)).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_isLeftAdjoint _
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (tilde.functor (.of A))
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- If `F ≅ M~|_U` is locally free, then at every point of `U = V(I)ᶜ` some localization of `M`
at a submonoid avoiding that point is projective. -/
private lemma exists_localized_projective_of_not_le (A : Type u) [CommRing A] (I : Ideal A)
    (U : (Spec (.of A)).Opens)
    (hU : (U : Set (Spec (.of A))) = (PrimeSpectrum.zeroLocus (I : Set A))ᶜ)
    (M : ModuleCat.{u} A) (F : (U : Scheme).Modules)
    [SheafOfModules.IsLocallyFree.{u, u, u} F] (e : F ≅ (tilde M).restrict U.ι)
    (q : PrimeSpectrum A) (hq : ¬ I ≤ q.asIdeal) :
    ∃ S : Submonoid A, S ≤ q.asIdeal.primeCompl ∧
      Module.Projective (Localization S) (LocalizedModule S M) := by
  have hqU : q ∈ (U : Set (Spec (.of A))) := by
    rw [hU]
    exact hq
  obtain ⟨f, hf, hfree⟩ := exists_basicOpen_localized_free A M U F e q hqU
  exact ⟨Submonoid.powers f, Submonoid.powers_le.mpr hf, Module.Projective.of_free⟩

end Extension

/-- Let `I` be a finitely generated ideal of `A`, let `J ≤ I` and let `U` be the complement of
`V(I)` in `Spec A`.  If a power of `J` annihilates the degree `p` cohomology of the structure
sheaf of `U`, then for every finite locally free sheaf `F` on `U` some power of `J` annihilates
the degree `p` cohomology of `F`.

Cohomology is the right derived functor of global sections, and the `A`-action is the one
induced by the canonical map `A ⟶ Γ(U, 𝒪_U)`. -/
@[stacks 0BM5]
theorem exists_pow_smul_derivedGlobalSections_eq_zero_of_isFiniteLocallyFree
    (A : Type u) [CommRing A] (I J : Ideal A) (hJI : J ≤ I) (hI : I.FG)
    (U : (Spec (.of A)).Opens)
    (hU : (U : Set (Spec (.of A))) = (PrimeSpectrum.zeroLocus (I : Set A))ᶜ) (p : ℕ)
    (hn : ∃ n : ℕ, ∀ a ∈ J ^ n,
      ∀ x : (ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (.of A)).inv ≫ U.ι.appTop).hom).obj
        (((SheafOfModules.evaluation (U : Scheme).ringCatSheaf
            (op (⊤ : (U : Scheme).Opens))).rightDerived p).obj
          (SheafOfModules.unit (U : Scheme).ringCatSheaf)), a • x = 0)
    (F : SheafOfModules (U : Scheme).ringCatSheaf)
    [SheafOfModules.IsFiniteLocallyFree.{u, u, u} F] :
    ∃ m : ℕ, ∀ a ∈ J ^ m,
      ∀ x : (ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (.of A)).inv ≫ U.ι.appTop).hom).obj
        (((SheafOfModules.evaluation (U : Scheme).ringCatSheaf
            (op (⊤ : (U : Scheme).Opens))).rightDerived p).obj F), a • x = 0 := by
  obtain ⟨n, hn⟩ := hn
  by_cases hp : p = 0
  · subst p
    exact ⟨n, fun a ha x => annihilates_sections_of_annihilates_unit (U : Scheme) A
      ((Scheme.ΓSpecIso (.of A)).inv ≫ U.ι.appTop).hom a (hn a ha) F x⟩
  · have : F.IsFinitePresentation := isFinitePresentation_of_isFiniteLocallyFree F
    obtain ⟨M, hMfp, ⟨e⟩⟩ := exists_finitePresentation_extension A I hI U hU F
    let c := ((Scheme.ΓSpecIso (.of A)).inv ≫ U.ι.appTop).hom
    let T : ModuleCat.{u} ↑(CommRingCat.of A) ⥤ SheafOfModules (U : Scheme).ringCatSheaf :=
      tilde.functor (.of A) ⋙ Scheme.Modules.restrictFunctor U.ι
    let S := SheafOfModules.evaluation (U : Scheme).ringCatSheaf (op (⊤ : (U : Scheme).Opens))
    let RS : ModuleCat.{u} ↑((U : Scheme).ringCatSheaf.obj.obj
        (op (⊤ : (U : Scheme).Opens))) ⥤ ModuleCat.{u} ↑(CommRingCat.of A) :=
      ModuleCat.restrictScalars c
    let G := S.rightDerived p ⋙ RS
    let H := T ⋙ G
    have hres : (Scheme.Modules.restrictFunctor U.ι).Additive :=
      Functor.additive_of_iso (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm
    have hder : (S.rightDerived p).Additive := rightDerived_additive S p
    have htil := tilde_functor_additive A
    have hT : T.Additive :=
      inferInstanceAs (tilde.functor (.of A) ⋙ Scheme.Modules.restrictFunctor U.ι).Additive
    have hrs : RS.Additive := { map_add := ModuleCat.hom_ext rfl }
    have hG : G.Additive := inferInstanceAs (S.rightDerived p ⋙ RS).Additive
    have hH : H.Additive := inferInstanceAs (T ⋙ G).Additive
    have hscalar (N : ModuleCat.{u} A) (a : A) : H.map (a • 𝟙 N) = a • 𝟙 (H.obj N) := by
      have h1 : (Scheme.Modules.restrictFunctor U.ι).map ((tilde.functor (.of A)).map (a • 𝟙 N)) =
          (scalarSheafNatTrans (U : Scheme) (U.ι.appTop ((Scheme.ΓSpecIso (.of A)).inv a))).app
              ((tilde N).restrict U.ι) :=
        (congrArg (Scheme.Modules.restrictFunctor U.ι).map (tilde_map_smul_id A N a)).trans
          (restrict_scalarSheafNatTrans U.ι ((Scheme.ΓSpecIso (.of A)).inv a) (tilde N))
      exact (congrArg
          (fun φ => (ModuleCat.restrictScalars c).map ((S.rightDerived p).map φ)) h1).trans
        (rightDerived_map_scalarSheafMap (U : Scheme) A c a p _)
    let eUnit : T.obj (ModuleCat.of A A) ≅ SheafOfModules.unit (U : Scheme).ringCatSheaf :=
      (Scheme.Modules.restrictFunctor U.ι).mapIso tildeSelf ≪≫ Scheme.Modules.restrictUnitIso U.ι
    have hring : ∀ a ∈ J ^ n, ∀ x : H.obj (ModuleCat.of A A), a • x = 0 := by
      exact fun a ha => smul_eq_zero_of_iso (G.mapIso eUnit) a (hn a ha)
    obtain ⟨m, hm⟩ := exists_pow_annihilates_linear_functor_obj H hscalar I J hI hJI n hring M
      (exists_localized_projective_of_not_le A I U hU M F e)
    exact ⟨m, fun a ha => smul_eq_zero_of_iso (G.mapIso e) a (hm a ha)⟩

end AlgebraicGeometry

end
