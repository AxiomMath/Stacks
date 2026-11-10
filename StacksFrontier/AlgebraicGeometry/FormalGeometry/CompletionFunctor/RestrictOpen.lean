module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicInverseSystem.Sections
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.RestrictOpen
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Completion commutes with restriction to an open subscheme

Let `f : Y ⟶ X` be an open immersion of locally Noetherian schemes, let `I` be a quasi-coherent
ideal sheaf on `X` and let `M` be a coherent `𝒪_X`-module. The completion functor of Stacks 0880
sends `M` to the inverse system `n ↦ M / I ^ (n+1) M` of coherent modules. Restricting that system
to `Y` term by term gives the completion of `M|_Y` along `I|_Y`.

The content is that the subsheaf `I ^ n M` restricts to `(I|_Y) ^ n (M|_Y)`. Both are computed on
an affine open `U ⊆ Y` by `Stacks.Algebraization.idealPowerMultiple_toSubmodule_obj_affine`, which
identifies the sections of an ideal-power multiple of a quasi-coherent module with the sectionwise
multiple; the ideal of `I|_Y` over `U` is the preimage of the ideal of `I` over `f(U)` under the
isomorphism `Γ(X, f(U)) ≅ Γ(Y, U)` induced by the open immersion, and the two sectionwise multiples
correspond under that isomorphism. Restriction is exact, so the induced maps on the quotients are
isomorphisms as well, and they are compatible with the transition maps of the inverse system
because both sides are compatible with the canonical projections out of `M`, which are
epimorphisms.

## Main definitions

* `Stacks.Algebraization.idealPowerMultipleRestrictMap` — the comparison map
  `(I ^ n M)|_Y ⟶ (I|_Y) ^ n (M|_Y)`.
* `Stacks.Algebraization.restrictCoherentModules` — the restriction of a coherent module along an
  open immersion, as an object of the category of coherent modules on the source.
* `Stacks.Algebraization.completionRestrictOpenIso` — the comparison isomorphism of inverse
  systems.

## Main results

* `Stacks.Algebraization.mem_idealPowerMultiple_restrict_affine_iff` — the affine-local
  description of the comparison.
* `Stacks.Algebraization.isIso_idealPowerMultipleRestrictMap` — the comparison map is an
  isomorphism.
* `Stacks.Algebraization.completionProjection_naturality` — the projections out of `M` onto the
  terms of its completion are compatible with every transition map, not only with the ones from
  `n + 1` to `n`.

## Implementation notes

`AlgebraicGeometry.Scheme.Modules` is a `def` for `SheafOfModules X.ringCatSheaf`, and the two
presentations carry separately declared instances, so several goals below mention an object with
two defeq but not syntactically equal spellings in its type. Such a goal is not type-correct at
the transparency a rewrite motive is built at, so `rw` cannot fire on it even with a lemma written
for it; the compatibility of the comparison isomorphisms with the projections and their
naturality are therefore assembled in term mode, out of `Category.assoc` and `congrArg`, and the
quasi-coherence of `M` is supplied as a hypothesis rather than left to instance search. None of this
relaxes definitional-equality transparency.

`cokernelMapIso_hom` and `cokernelπ_map` restate two `rfl`-level facts about
`CategoryTheory.Limits.cokernel.mapIso` as named lemmas, so that the proofs below can name a
theorem rather than unfold a Mathlib definition inside a `simp only` set, which would mint that
definition's equation lemma into this module.

## References

* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
* [Stacks Project, Tag 0EI8](https://stacks.math.columbia.edu/tag/0EI8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace Stacks.Algebraization

/-- A semilinear additive map sends `J • ⊤` into `K • ⊤` when the ring map sends `J` into `K`. -/
private theorem smul_top_mem_of_semilinear {R S M N : Type*} [CommRing R] [CommRing S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N] {F : Type*} [FunLike F M N]
    [AddMonoidHomClass F M N] (φ : R →+* S) (g : F)
    (hg : ∀ (a : R) (x : M), g (a • x) = φ a • g x) {J : Ideal R} {K : Ideal S}
    (hJ : ∀ a ∈ J, φ a ∈ K) {x : M} (hx : x ∈ J • (⊤ : Submodule R M)) :
    g x ∈ K • (⊤ : Submodule S N) := by
  refine Submodule.smul_induction_on hx (fun a ha z _ => ?_) fun x y hx hy => ?_
  · rw [hg]
    exact Submodule.smul_mem_smul (hJ a ha) Submodule.mem_top
  · rw [map_add]
    exact Submodule.add_mem _ hx hy

/-- Membership in `I ^ n M` over an affine open of `Y` is membership of the transported section
in `I ^ n M` over its image in `X`. -/
public lemma mem_idealPowerMultiple_restrict_affine_iff {X Y : Scheme.{u}}
    (f : Y ⟶ X) [IsOpenImmersion f] (I : X.IdealSheafData)
    (n : ℕ) (M : X.Modules) [M.IsQuasicoherent]
    (U : Y.affineOpens) (s : Γ(M.restrict f, U.1)) :
    s ∈ (idealPowerMultiple (I.comap f) n (M.restrict f)).toSubmodule.obj (op U.1) ↔
      (M.restrictAppIso f U.1).hom s ∈
        (idealPowerMultiple I n M).toSubmodule.obj (op (f ''ᵁ U.1)) := by
  have hQ : (M.restrict f).IsQuasicoherent := Scheme.Modules.isQuasicoherent_restrictFunctor f M
  let W : X.affineOpens := ⟨f ''ᵁ U.1, U.2.image_of_isOpenImmersion f⟩
  rw [idealPowerMultiple_toSubmodule_obj_affine (I.comap f) n (M.restrict f) U,
    show (idealPowerMultiple I n M).toSubmodule.obj (op (f ''ᵁ U.1)) =
      I.ideal W ^ n • (⊤ : Submodule Γ(X, W.1) Γ(M, W.1)) from
      idealPowerMultiple_toSubmodule_obj_affine I n M W]
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  let e := (f.appIso U.1).commRingCatIsoToRingEquiv
  have hp : Ideal.comap (f.appIso U.1).inv.hom (I.ideal W) ^ n =
      Ideal.comap (f.appIso U.1).inv.hom (I.ideal W ^ n) := by
    change Ideal.comap e.symm (I.ideal W) ^ n =
      Ideal.comap e.symm (I.ideal W ^ n)
    rw [← Ideal.map_comap_of_equiv e, ← Ideal.map_comap_of_equiv e, Ideal.map_pow]
  rw [hp]
  let eM : Γ(M.restrict f, U.1) ≃+ Γ(M, f ''ᵁ U.1) :=
    (M.restrictAppIso f U.1).addCommGroupIsoToAddEquiv
  have hcompat (a : Γ(Y, U.1)) (x : Γ(M.restrict f, U.1)) :
      eM (a • x) = e.symm a • eM x :=
    Scheme.Modules.smul_restrictAppIso_hom_apply f M U.1 a x
  have hforward : ∀ x : Γ(M.restrict f, U.1),
      x ∈ Ideal.comap (e.symm : Γ(Y, U.1) →+* Γ(X, f ''ᵁ U.1))
          (I.ideal W ^ n) • (⊤ : Submodule Γ(Y, U.1) Γ(M.restrict f, U.1)) →
      eM x ∈ I.ideal W ^ n • (⊤ : Submodule Γ(X, f ''ᵁ U.1) Γ(M, f ''ᵁ U.1)) :=
    fun x hx => smul_top_mem_of_semilinear (e.symm : Γ(Y, U.1) →+* Γ(X, f ''ᵁ U.1)) eM
      hcompat (fun a ha => Ideal.mem_comap.mp ha) hx
  refine ⟨hforward s, fun hs => ?_⟩
  have hcompat' (a : Γ(X, f ''ᵁ U.1)) (x : Γ(M, f ''ᵁ U.1)) :
      eM.symm (a • x) = e a • eM.symm x := by
    apply eM.injective
    rw [eM.apply_symm_apply, hcompat, e.symm_apply_apply, eM.apply_symm_apply]
  have hreverse : eM.symm (eM s) ∈ Ideal.comap (e.symm : Γ(Y, U.1) →+* Γ(X, f ''ᵁ U.1))
      (I.ideal W ^ n) • (⊤ : Submodule Γ(Y, U.1) Γ(M.restrict f, U.1)) :=
    smul_top_mem_of_semilinear (e : Γ(X, f ''ᵁ U.1) →+* Γ(Y, U.1)) eM.symm hcompat'
      (fun a ha => by
        change e.symm (e a) ∈ I.ideal W ^ n
        rwa [e.symm_apply_apply]) hs
  change s ∈ Ideal.comap (e.symm : Γ(Y, U.1) →+* Γ(X, f ''ᵁ U.1))
    (I.ideal W ^ n) • (⊤ : Submodule Γ(Y, U.1) Γ(M.restrict f, U.1))
  simpa only [eM.symm_apply_apply] using hreverse


/-- Restriction along an open immersion carries `I ^ n M` into `(I|_Y) ^ n (M|_Y)`. -/
public noncomputable def idealPowerMultipleRestrictMap {X Y : Scheme.{u}}
    (f : Y ⟶ X) [IsOpenImmersion f] (I : X.IdealSheafData)
    (n : ℕ) (M : X.Modules) [M.IsQuasicoherent] :
    (Scheme.Modules.restrictFunctor f).obj
      (idealPowerMultiple I n M).toSheafOfModules ⟶
      (idealPowerMultiple (I.comap f) n (M.restrict f)).toSheafOfModules := by
  let P := idealPowerMultiple I n M
  let Q := idealPowerMultiple (I.comap f) n (M.restrict f)
  let R := Scheme.Modules.restrictFunctor f
  let ι := R.map P.ι
  have hmem (W : Y.Opens) (x : Γ(R.obj P.toSheafOfModules, W)) :
      ι.app W x ∈ Q.toSubmodule.obj (op W) := by
    apply mem_submodule_of_affine Q W
    intro A i
    have hAW : (A : Y.Opens) ≤ W := leOfHom i
    have hnat := congrArg (fun g => g x) (ι.mapPresheaf.naturality (homOfLE hAW).op)
    have hx : (M.restrictAppIso f A.1).hom
        (ι.app A.1 ((R.obj P.toSheafOfModules).presheaf.map
          (homOfLE hAW).op x)) ∈ P.toSubmodule.obj (op (f ''ᵁ A.1)) := by
      change ((R.obj P.toSheafOfModules).presheaf.map
          (homOfLE hAW).op x).1 ∈ P.toSubmodule.obj (op (f ''ᵁ A.1))
      exact ((R.obj P.toSheafOfModules).presheaf.map
          (homOfLE hAW).op x).property
    have hy := (mem_idealPowerMultiple_restrict_affine_iff f I n M A _).mpr hx
    have hres : (M.restrict f).presheaf.map (homOfLE hAW).op (ι.app W x) =
        ι.app A.1 ((R.obj P.toSheafOfModules).presheaf.map (homOfLE hAW).op x) := hnat
    have hi : i = homOfLE hAW := Subsingleton.elim _ _
    subst hi
    exact hres ▸ hy
  refine ⟨{ app := fun W => (ConcreteCategory.ofHom (C := ModuleCat Γ(Y, W.unop))
      (((ι.val.app W).hom).codRestrict (Q.toSubmodule.obj W)
        (fun x => hmem W.unop x))), naturality := ?_ }⟩
  intro W Z g
  ext x
  exact Subtype.ext (congrArg (fun k => k x) (ι.mapPresheaf.naturality g))


/-- The comparison map acts on sections as the inclusion of `I ^ n M` does. -/
public lemma idealPowerMultipleRestrictMap_app_coe {X Y : Scheme.{u}}
    (f : Y ⟶ X) [IsOpenImmersion f] (I : X.IdealSheafData)
    (n : ℕ) (M : X.Modules) [M.IsQuasicoherent] (W : Y.Opens)
    (x : Γ((Scheme.Modules.restrictFunctor f).obj
      (idealPowerMultiple I n M).toSheafOfModules, W)) :
    Subtype.val ((idealPowerMultipleRestrictMap f I n M).app W x) =
      ((Scheme.Modules.restrictFunctor f).map (idealPowerMultiple I n M).ι).app W x :=
  rfl

/-- The comparison map `(I ^ n M)|_Y ⟶ (I|_Y) ^ n (M|_Y)` is an isomorphism. -/
public lemma isIso_idealPowerMultipleRestrictMap {X Y : Scheme.{u}}
    (f : Y ⟶ X) [IsOpenImmersion f] (I : X.IdealSheafData)
    (n : ℕ) (M : X.Modules) [M.IsQuasicoherent] :
    IsIso (idealPowerMultipleRestrictMap f I n M) := by
  let p := idealPowerMultipleRestrictMap f I n M
  have hp : IsIso ((SheafOfModules.toSheaf Y.ringCatSheaf).map p) := by
    have hb : Opens.IsBasis (Set.range (fun A : Y.affineOpens => A.1)) := by
      rw [Subtype.range_coe]
      exact Y.isBasis_affineOpens
    apply TopCat.Sheaf.isIso_iff_isIso_basis hb
    intro A
    apply (ConcreteCategory.isIso_iff_bijective _).2
    constructor
    · intro a b hab
      apply Subtype.ext
      have ha := idealPowerMultipleRestrictMap_app_coe f I n M A.1 a
      have hb' := idealPowerMultipleRestrictMap_app_coe f I n M A.1 b
      exact ha.symm.trans ((congrArg Subtype.val hab).trans hb')
    · intro s
      have hs : (M.restrictAppIso f A.1).hom s.val ∈
          (idealPowerMultiple I n M).toSubmodule.obj (op (f ''ᵁ A.1)) :=
        (mem_idealPowerMultiple_restrict_affine_iff f I n M A s.val).mp s.property
      exact ⟨⟨s.val, hs⟩, rfl⟩
  apply (Scheme.Modules.Hom.isIso_iff_isIso_app).mpr
  intro W
  let T := (SheafOfModules.toSheaf Y.ringCatSheaf).map p
  have hT : IsIso T.hom := by
    have : IsIso T := hp
    infer_instance
  exact (NatTrans.isIso_iff_isIso_app T.hom).mp hT (op W)


/-- The projections onto the terms of the completion are compatible with every transition map of
the inverse system. -/
public theorem completionProjection_naturality {X : Scheme.{u}}
    [IsLocallyNoetherian X] (I : X.IdealSheafData)
    (M : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    {i j : ℕᵒᵖ} (g : i ⟶ j) :
    completionProjection X I M i.unop ≫
      ((completionFunctor X I).obj M).obj.map g = completionProjection X I M j.unop := by
  have hpath (n m : ℕ) (h : n ≤ m) :
      completionProjection X I M m ≫
        ((completionFunctor X I).obj M).obj.map (homOfLE h).op =
          completionProjection X I M n := by
    induction m, h using Nat.le_induction with
    | base =>
      have h1 : ((completionFunctor X I).obj M).obj.map
          (homOfLE (le_refl n)).op = 𝟙 _ :=
        ((completionFunctor X I).obj M).obj.map_id (op n)
      exact (congrArg (fun h => completionProjection X I M n ≫ h) h1).trans
        (Category.comp_id _)
    | succ m hm ih =>
      have heq : (homOfLE (Nat.le_succ m)).op ≫ (homOfLE hm).op =
          (homOfLE (hm.trans (Nat.le_succ m))).op := rfl
      rw [← heq, Functor.map_comp]
      calc
        _ = (completionProjection X I M (m + 1) ≫
              ((completionFunctor X I).obj M).obj.map (homOfLE (Nat.le_succ m)).op) ≫
              ((completionFunctor X I).obj M).obj.map (homOfLE hm).op := rfl
        _ = _ := by rw [completionProjection_transition]; exact ih
  have hg : g = (homOfLE (leOfHom g.unop)).op := Subsingleton.elim _ _
  rw [hg]
  exact hpath j.unop i.unop (leOfHom g.unop)


/-- The restriction to `Y` of the coherent module `M`, as an object of the category of coherent
modules on `Y`. -/
public noncomputable def restrictCoherentModules {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] [IsLocallyNoetherian X]
    (M : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) :
    AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf :=
  ⟨(Scheme.Modules.restrictFunctor f).obj M.obj,
    @isCoherent_restrict_of_isOpenImmersion X Y f ‹_› ‹_› M.obj M.property⟩

/-- `(cokernel.mapIso _ _ p q w).hom` is the induced map on cokernels. -/
public lemma cokernelMapIso_hom {C : Type*} [Category C] [Limits.HasZeroMorphisms C]
    {A B : C} (g : A ⟶ B) [HasCokernel g] {A' B' : C} (g' : A' ⟶ B') [HasCokernel g']
    (α : A ≅ A') (β : B ≅ B') (w : g ≫ β.hom = α.hom ≫ g') :
    (cokernel.mapIso g g' α β w).hom = cokernel.map g g' α.hom β.hom w :=
  rfl

/-- The projection out of a cokernel composed with an induced map on cokernels. -/
public lemma cokernelπ_map {C : Type*} [Category C] [Limits.HasZeroMorphisms C]
    {A B : C} (g : A ⟶ B) [HasCokernel g] {A' B' : C} (g' : A' ⟶ B') [HasCokernel g']
    (α : A ⟶ A') (β : B ⟶ B') (w : g ≫ β = α ≫ g') :
    cokernel.π g ≫ cokernel.map g g' α β w = β ≫ cokernel.π g' :=
  cokernel.π_desc _ _ _

/-- **Completion commutes with restriction to an open.** For an open immersion `f : Y ⟶ X` of
locally Noetherian schemes and a coherent module `M` on `X`, restricting the completion of `M`
along `I` term by term gives the completion of `M|_Y` along `I|_Y`.

Each term is the quotient of `M` by a power of `I`, restriction is exact, and it carries `I ^ n M`
isomorphically onto `(I|_Y) ^ n (M|_Y)`; the resulting isomorphisms of terms are compatible with
the transition maps because both sides are compatible with the canonical projections out of `M`,
which are epimorphisms. -/
@[ega "III 5.2.6" "partial"]
public noncomputable def completionRestrictOpenIso {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (I : X.IdealSheafData)
    (M : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) :
    (((completionFunctor X I).obj M).obj ⋙ Scheme.Modules.restrictFunctor f) ≅
      ((completionFunctor Y (I.comap f)).obj (restrictCoherentModules f M)).obj := by
  have hMq : M.obj.IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent M.obj).1
  let R : Scheme.Modules X ⥤ Scheme.Modules Y := Scheme.Modules.restrictFunctor f
  let N : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf :=
    restrictCoherentModules f M
  have hIso : ∀ n : ℕ, IsIso (idealPowerMultipleRestrictMap f I (n + 1) M.obj) :=
    fun n => isIso_idealPowerMultipleRestrictMap f I (n + 1) M.obj
  have hpRestrict : ∀ n : ℕ, R.map ((idealPowerMultiple I (n + 1) M.obj).ι) =
      idealPowerMultipleRestrictMap f I (n + 1) M.obj ≫
        (idealPowerMultiple (I.comap f) (n + 1) (R.obj M.obj)).ι := by
    intro n
    ext W x
    rfl
  let c : ∀ n : ℕ, R.obj (((completionFunctor X I).obj M).obj.obj (op n)) ≅
      ((completionFunctor Y (I.comap f)).obj N).obj.obj (op n) := fun n =>
    R.mapIso (eqToIso (completionFunctor_obj X I M n)) ≪≫
      PreservesCokernel.iso R ((idealPowerMultiple I (n + 1) M.obj).ι) ≪≫
        cokernel.mapIso (R.map ((idealPowerMultiple I (n + 1) M.obj).ι))
          ((idealPowerMultiple (I.comap f) (n + 1) (R.obj M.obj)).ι)
          (asIso (idealPowerMultipleRestrictMap f I (n + 1) M.obj))
          (Iso.refl (R.obj M.obj)) (hpRestrict n) ≪≫
        (eqToIso (completionFunctor_obj Y (I.comap f) N n)).symm
  have hc : ∀ n : ℕ, R.map (completionProjection X I M n) ≫ (c n).hom =
      completionProjection Y (I.comap f) N n := by
    intro n
    have hinner : completionProjection X I M n ≫ eqToHom (completionFunctor_obj X I M n) =
        cokernel.π ((idealPowerMultiple I (n + 1) M.obj).ι) :=
      (Category.assoc (cokernel.π ((idealPowerMultiple I (n + 1) M.obj).ι))
          (eqToHom (completionFunctor_obj X I M n).symm)
          (eqToHom (completionFunctor_obj X I M n))).trans
        ((congrArg (fun k => cokernel.π ((idealPowerMultiple I (n + 1) M.obj).ι) ≫ k)
            ((eqToHom_trans _ _).trans (eqToHom_refl _ _))).trans (Category.comp_id _))
    have t1 : R.map (completionProjection X I M n) ≫
        R.map (eqToHom (completionFunctor_obj X I M n)) =
          R.map (cokernel.π ((idealPowerMultiple I (n + 1) M.obj).ι)) :=
      (R.map_comp _ _).symm.trans (congrArg R.map hinner)
    have t2 : R.map (cokernel.π ((idealPowerMultiple I (n + 1) M.obj).ι)) ≫
        (PreservesCokernel.iso R ((idealPowerMultiple I (n + 1) M.obj).ι)).hom =
          cokernel.π (R.map ((idealPowerMultiple I (n + 1) M.obj).ι)) :=
      PreservesCokernel.π_iso_hom R ((idealPowerMultiple I (n + 1) M.obj).ι)
    have t3 : cokernel.π (R.map ((idealPowerMultiple I (n + 1) M.obj).ι)) ≫
        cokernel.map (R.map ((idealPowerMultiple I (n + 1) M.obj).ι))
          ((idealPowerMultiple (I.comap f) (n + 1) (R.obj M.obj)).ι)
          (asIso (idealPowerMultipleRestrictMap f I (n + 1) M.obj)).hom
          (Iso.refl (R.obj M.obj)).hom (hpRestrict n) =
            cokernel.π ((idealPowerMultiple (I.comap f) (n + 1) (R.obj M.obj)).ι) :=
      (cokernelπ_map _ _ _ _ (hpRestrict n)).trans (Category.id_comp _)
    simp only [c, Iso.trans_hom, Functor.mapIso_hom, eqToIso.hom, ← Category.assoc]
    rw [t1]
    exact (congrArg (fun q => q ≫
        (cokernel.mapIso (R.map ((idealPowerMultiple I (n + 1) M.obj).ι))
            ((idealPowerMultiple (I.comap f) (n + 1) (R.obj M.obj)).ι)
            (asIso (idealPowerMultipleRestrictMap f I (n + 1) M.obj))
            (Iso.refl (R.obj M.obj)) (hpRestrict n) ≪≫
          (eqToIso (completionFunctor_obj Y (I.comap f) N n)).symm).hom) t2).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun q => q ≫ eqToHom (completionFunctor_obj Y (I.comap f) N n).symm) t3))
  refine NatIso.ofComponents (fun n => c n.unop) ?_
  intro i j g
  have hπ : Epi (R.map (cokernel.π ((idealPowerMultiple I (i.unop + 1) M.obj).ι))) := by
    have hepi2 : Epi (PreservesCokernel.iso R
        ((idealPowerMultiple I (i.unop + 1) M.obj).ι)).inv := IsIso.epi_of_iso _
    have hfac : cokernel.π (R.map ((idealPowerMultiple I (i.unop + 1) M.obj).ι)) ≫
          (PreservesCokernel.iso R ((idealPowerMultiple I (i.unop + 1) M.obj).ι)).inv =
        R.map (cokernel.π ((idealPowerMultiple I (i.unop + 1) M.obj).ι)) :=
      ((Iso.eq_comp_inv _).2
        (PreservesCokernel.π_iso_hom R ((idealPowerMultiple I (i.unop + 1) M.obj).ι))).symm
    exact hfac ▸ epi_comp' inferInstance hepi2
  have hepi : Epi (R.map (completionProjection X I M i.unop)) := by
    have hiso3 : IsIso (R.map (eqToHom (completionFunctor_obj X I M i.unop).symm)) :=
      Functor.map_isIso R (eqToHom (completionFunctor_obj X I M i.unop).symm)
    have hepi3 : Epi (R.map (eqToHom (completionFunctor_obj X I M i.unop).symm)) :=
      IsIso.epi_of_iso _
    have h2 : R.map (cokernel.π ((idealPowerMultiple I (i.unop + 1) M.obj).ι)) ≫
          R.map (eqToHom (completionFunctor_obj X I M i.unop).symm) =
        R.map (completionProjection X I M i.unop) := (R.map_comp _ _).symm
    exact h2 ▸ epi_comp' hπ hepi3
  apply (cancel_epi (R.map (completionProjection X I M i.unop))).mp
  change R.map (completionProjection X I M i.unop) ≫
      (R.map (((completionFunctor X I).obj M).obj.map g) ≫ (c j.unop).hom) =
    R.map (completionProjection X I M i.unop) ≫
      ((c i.unop).hom ≫ ((completionFunctor Y (I.comap f)).obj N).obj.map g)
  have step1 : R.map (completionProjection X I M i.unop) ≫
      R.map (((completionFunctor X I).obj M).obj.map g) =
        R.map (completionProjection X I M j.unop) :=
    (R.map_comp _ _).symm.trans
      (congrArg R.map (completionProjection_naturality I M g))
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun q => q ≫ (c j.unop).hom) step1) ?_
  refine Eq.trans (hc j.unop) ?_
  refine Eq.trans (completionProjection_naturality (I.comap f) N g).symm ?_
  refine Eq.trans (congrArg (fun q => q ≫
    ((completionFunctor Y (I.comap f)).obj N).obj.map g) (hc i.unop).symm) ?_
  exact Category.assoc _ _ _

end Stacks.Algebraization

end
