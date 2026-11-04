module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.LocalConstancy
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.Sequence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Artin–Schreier sequence `0 ⟶ 𝐙/p𝐙 ⟶ 𝐆_a ⟶ 𝐆_a ⟶ 0`

For a scheme `X` of characteristic `p` the kernel of the Artin–Schreier map `x ↦ x ^ p - x` on
`𝐆_a` is the constant sheaf `𝐙/p𝐙` on the small étale site, so that

`0 ⟶ 𝐙/p𝐙 ⟶ 𝐆_a ⟶ 𝐆_a ⟶ 0`

is a short exact sequence of abelian sheaves.

The inclusion is the sheafification of the map of presheaves sending a residue class to the
corresponding scalar function. It is locally injective because two distinct scalars differ by a
unit, so they can agree only on a scheme with no points; it is locally surjective onto the kernel
because a global function with `x ^ p = x` is locally one of the `p` scalars.

## Main definitions

* `Stacks.ArtinSchreier.zmodSheafHom`: the inclusion `𝐙/p𝐙 ⟶ 𝐆_a`.
* `Stacks.ArtinSchreier.constantArtinSchreierSequence`: the short complex
  `𝐙/p𝐙 ⟶ 𝐆_a ⟶ 𝐆_a`.

## Main results

* `Stacks.ArtinSchreier.exists_etale_natCast_of_point`: a global function with `x ^ p = x` is
  étale-locally a scalar.
* `Stacks.ArtinSchreier.constantArtinSchreierSequence_shortExact`: **the Artin–Schreier sequence
  is short exact.**

## Implementation notes

At the coefficient universe `v = u + 1` the left term is
`Stacks.ArtinSchreier.etaleConstantZMod X p`; the statement here is polymorphic in `v` and
specialises to it.

The map out of `𝐙/p𝐙` is built with `ZMod.lift` rather than `ZMod.castHom`: the latter needs
`CharP Γ(U, 𝒪_U) p`, which fails on the empty étale `X`-scheme, where the ring is zero and the
characteristic is `1`. Only the additive structure is needed, and `ZMod.lift` asks only that `p`
times the generator vanish.

Exactness in the middle is obtained by showing that the comparison into `kernel (F - 1)` is
locally surjective. Sections of that kernel are handled only through `kernel.ι`, which is
injective on sections because `sheafToPresheaf` and evaluation both preserve limits; so every
equation is checked in `𝐆_a`, whose sections are global functions.

## References

* [Stacks Project, Tag 0A3J](https://stacks.math.columbia.edu/tag/0A3J): the Artin–Schreier
  sequence.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v

namespace Stacks.ArtinSchreier

/-- Two additive maps out of `ZMod n` agreeing at the generator are equal. -/
theorem addMonoidHom_ext_zmod {n : ℕ} {A : Type*} [AddGroup A] (f g : ZMod n →+ A)
    (h : f 1 = g 1) : f = g := by
  ext y
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective y
  rw [show ((k : ℤ) : ZMod n) = k • (1 : ZMod n) by simp [zsmul_eq_mul], map_zsmul, map_zsmul, h]

/-- A scheme whose ring of global functions is zero has no points. -/
theorem isEmpty_of_zero_eq_one (Y : Scheme.{u}) (h : (0 : Γ(Y, ⊤)) = 1) : IsEmpty Y := by
  refine ⟨fun t => ?_⟩
  obtain ⟨R, g, -, y₀, -⟩ := Scheme.exists_Spec_apply_eq t
  have := PrimeSpectrum.nontrivial (R := R) y₀
  have hmap := congrArg (g.appTop ≫ (Scheme.ΓSpecIso R).hom).hom h
  rw [map_zero, map_one] at hmap
  exact zero_ne_one hmap

/-- Every sieve on an étale `X`-scheme with no points is covering. -/
theorem mem_smallEtaleTopology_of_isEmpty (X : Scheme.{u}) (U : X.Etale) (hU : IsEmpty U.left)
    (S : Sieve U) : S ∈ X.smallEtaleTopology U := by
  have hcov : Sieve.ofArrows (fun _ : PEmpty.{u + 1} => U) (fun i => i.elim) ∈
      X.smallEtaleTopology U := by
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    exact Set.eq_univ_of_forall fun t => hU.elim t
  refine X.smallEtaleTopology.superset_covering ?_ hcov
  rw [Sieve.ofArrows, Sieve.generate_le_iff]
  rintro V - ⟨i⟩
  exact i.elim

/-- **A solution of `x ^ p = x` is étale-locally a scalar.** Through every point of an étale
`X`-scheme `U` there is an étale morphism over which a given global function with `x ^ p = x`
becomes one of the `p` constants. -/
theorem exists_etale_natCast_of_point (X : Scheme.{u}) {p : ℕ} (hp : p.Prime)
    (hX : (p : Γ(X, ⊤)) = 0) (U : X.Etale) (x : Γ(U.left, ⊤)) (hx : x ^ p = x) (t : U.left) :
    ∃ (W : Scheme.{u}) (g : W ⟶ U.left) (_ : Etale g) (i : ℕ),
      t ∈ Set.range g.base ∧ g.appTop.hom x = (i : Γ(W, ⊤)) := by
  obtain ⟨R, h, hh, y₀, hy₀⟩ := Scheme.exists_Spec_apply_eq t
  let q : PrimeSpectrum R := y₀
  obtain ⟨a, ha⟩ : ∃ a : R, (Scheme.ΓSpecIso R).inv.hom a = h.appTop.hom x :=
    ⟨(Scheme.ΓSpecIso R).hom.hom (h.appTop.hom x), by simp⟩
  have hpR : (p : R) = 0 :=
    (map_natCast (h.appTop ≫ (Scheme.ΓSpecIso R).hom).hom p).symm.trans
      ((congrArg (h.appTop ≫ (Scheme.ΓSpecIso R).hom).hom
        (natCast_eq_zero_of_etale X hX U)).trans (map_zero _))
  have haR : a ^ p = a := by
    have key : (Scheme.ΓSpecIso R).inv.hom (a ^ p) = (Scheme.ΓSpecIso R).inv.hom a := by
      rw [map_pow, ha, ← map_pow, hx]
    simpa using congrArg (Scheme.ΓSpecIso R).hom.hom key
  obtain ⟨i, f, -, hf, heq⟩ := exists_notMem_and_algebraMap_eq hp hpR a haR q.asIdeal
  let ϕ : R ⟶ CommRingCat.of (Localization.Away f) :=
    CommRingCat.ofHom (algebraMap R (Localization.Away f))
  have hopen : IsOpenImmersion (Spec.map ϕ) :=
    Scheme.isOpenImmersion_SpecMap_localizationAway f
  refine ⟨Spec (CommRingCat.of (Localization.Away f)), Spec.map ϕ ≫ h, inferInstance, i, ?_, ?_⟩
  · have hy : y₀ ∈ Set.range (Spec.map ϕ).base := by
      rw [show Set.range (Spec.map ϕ).base =
          Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away f))) from rfl,
        PrimeSpectrum.localization_away_comap_range (Localization.Away f) f]
      exact hf
    obtain ⟨z, hz⟩ := hy
    exact ⟨z, by rw [show (Spec.map ϕ ≫ h) z = h ((Spec.map ϕ) z) from rfl, hz, hy₀]⟩
  · have hnat : (Spec.map ϕ).appTop.hom ((Scheme.ΓSpecIso R).inv.hom a) =
        (Scheme.ΓSpecIso (CommRingCat.of (Localization.Away f))).inv.hom (ϕ.hom a) :=
      (congrArg
        (fun (k : R ⟶ Γ(Spec (CommRingCat.of (Localization.Away f)), ⊤)) => k.hom a)
        (Scheme.ΓSpecIso_inv_naturality ϕ)).symm
    rw [show (Spec.map ϕ ≫ h).appTop.hom x = (Spec.map ϕ).appTop.hom (h.appTop.hom x) from rfl,
      ← ha, hnat, show ϕ.hom a = ((i : ℕ) : Localization.Away f) from heq, map_natCast]

section Comparison

variable (X : Scheme.{u}) {p : ℕ} (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0)

/-- The scalar attached to a residue class, as an additive map `𝐙/p𝐙 →+ Γ(U, 𝒪_U)`. It exists
because `p` vanishes on `U`, and only the additive structure of `𝐙/p𝐙` is used. -/
def constZModHom (U : X.Etale) : ZMod p →+ Γ(U.left, ⊤) :=
  ZMod.lift p ⟨Int.castAddHom Γ(U.left, ⊤), by
    simpa using natCast_eq_zero_of_etale X hX U⟩

/-- The scalar attached to the class of an integer `k` is `k`. -/
@[simp]
theorem constZModHom_intCast (U : X.Etale) (k : ℤ) :
    constZModHom X hX U ((k : ℤ) : ZMod p) = (k : Γ(U.left, ⊤)) :=
  ZMod.lift_coe _ _ k

/-- The scalar attached to the class of a natural number `k` is `k`. -/
theorem constZModHom_natCast (U : X.Etale) (k : ℕ) :
    constZModHom X hX U ((k : ℕ) : ZMod p) = (k : Γ(U.left, ⊤)) := by
  simpa using constZModHom_intCast X hX U (k : ℤ)

/-- The scalar attached to `1` is `1`. -/
theorem constZModHom_one (U : X.Etale) : constZModHom X hX U 1 = 1 := by
  simpa using constZModHom_intCast X hX U 1

/-- Restricting the scalar attached to a residue class along `V ⟶ U` gives the scalar attached
to it on `V`. -/
theorem constZModHom_naturality {U V : X.Etale} (g : V ⟶ U) (m : ZMod p) :
    g.left.appTop.hom (constZModHom X hX U m) = constZModHom X hX V m := by
  have h := addMonoidHom_ext_zmod
    ((g.left.appTop.hom.toAddMonoidHom).comp (constZModHom X hX U)) (constZModHom X hX V)
    (by simp [constZModHom_one])
  exact DFunLike.congr_fun h m

include hp in
/-- **A scalar is fixed by Frobenius**: `c ^ p = c` for `c` the function attached to a residue
class. This is Fermat's little theorem read in a ring of characteristic `p`. -/
theorem constZModHom_pow (U : X.Etale) (m : ZMod p) :
    (constZModHom X hX U m) ^ p = constZModHom X hX U m := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective m
  rw [constZModHom_intCast]
  obtain ⟨c, hc⟩ : (p : ℤ) ∣ k ^ p - k :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (by push_cast; rw [ZMod.pow_card, sub_self])
  have hzero : ((k ^ p - k : ℤ) : Γ(U.left, ⊤)) = 0 := by
    rw [hc]
    push_cast
    rw [natCast_eq_zero_of_etale X hX U, zero_mul]
  push_cast at hzero
  exact sub_eq_zero.mp hzero

/-- The map of presheaves from the constant presheaf `𝐙/p𝐙` to `𝐆_a` sending a residue class to
the corresponding scalar function. -/
def zmodPresheafHom :
    (Functor.const X.Etaleᵒᵖ).obj
        (AddCommGrpCat.of (ULift.{max (u + 1) v} (ZMod p))) ⟶ additivePresheaf.{u, v} X where
  app U := AddCommGrpCat.ofHom
    (AddMonoidHom.mk' (fun m : ULift.{max (u + 1) v} (ZMod p) =>
        ULift.up (constZModHom X hX U.unop m.down))
      (fun a b => congrArg ULift.up (map_add (constZModHom X hX U.unop) a.down b.down)))
  naturality _ _ g := by
    ext m
    exact congrArg ULift.up (constZModHom_naturality X hX g.unop m.down).symm

/-- On sections over `U`, `zmodPresheafHom` sends a residue class `m` to the scalar function
`constZModHom X hX U m`. -/
@[simp]
theorem zmodPresheafHom_app (U : X.Etale) (m : ZMod p) :
    (zmodPresheafHom.{u, v} X hX).app (op U) (ULift.up m) =
      ofSection.{u, v} (constZModHom X hX U m) :=
  rfl

/-- **The inclusion `𝐙/p𝐙 ⟶ 𝐆_a`** on the small étale site of a scheme of characteristic `p`,
the sheafification of `Stacks.ArtinSchreier.zmodPresheafHom`. -/
def zmodSheafHom :
    (constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj
        (AddCommGrpCat.of (ULift.{max (u + 1) v} (ZMod p))) ⟶ additiveSheaf.{u, v} X :=
  ⟨sheafifyLift X.smallEtaleTopology (zmodPresheafHom.{u, v} X hX)
    (isSheaf_additivePresheaf.{u, v} X)⟩

/-- Precomposed with the sheafification map, `zmodSheafHom` is `zmodPresheafHom`. -/
theorem toSheafify_zmodSheafHom :
    toSheafify X.smallEtaleTopology
        ((Functor.const X.Etaleᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{max (u + 1) v} (ZMod p)))) ≫
        (zmodSheafHom.{u, v} X hX).hom = zmodPresheafHom.{u, v} X hX :=
  toSheafify_sheafifyLift _ _ _

include hp in
/-- The composite `𝐙/p𝐙 ⟶ 𝐆_a ⟶ 𝐆_a` of presheaves vanishes. -/
theorem zmodPresheafHom_comp_artinSchreierMap :
    zmodPresheafHom.{u, v} X hX ≫ (artinSchreierMap.{u, v} X hp hX).hom = 0 := by
  ext U m
  show ULift.up ((constZModHom X hX U.unop m.down) ^ p - constZModHom X hX U.unop m.down) = _
  rw [constZModHom_pow X hp hX U.unop m.down, sub_self]
  rfl

include hp in
/-- The composite `𝐙/p𝐙 ⟶ 𝐆_a ⟶ 𝐆_a` of sheaves vanishes. -/
theorem zmodSheafHom_comp_artinSchreierMap :
    zmodSheafHom.{u, v} X hX ≫ artinSchreierMap.{u, v} X hp hX = 0 := by
  refine Sheaf.hom_ext (sheafify_hom_ext X.smallEtaleTopology _ _
    (isSheaf_additivePresheaf.{u, v} X) ?_)
  show toSheafify X.smallEtaleTopology
      ((Functor.const X.Etaleᵒᵖ).obj
        (AddCommGrpCat.of (ULift.{max (u + 1) v} (ZMod p)))) ≫
      (zmodSheafHom.{u, v} X hX).hom ≫ (artinSchreierMap.{u, v} X hp hX).hom =
    toSheafify X.smallEtaleTopology
      ((Functor.const X.Etaleᵒᵖ).obj
        (AddCommGrpCat.of (ULift.{max (u + 1) v} (ZMod p)))) ≫ 0
  refine Eq.trans (Category.assoc _ _ _).symm (Eq.trans ?_ comp_zero.symm)
  exact Eq.trans
    (congrArg (· ≫ (artinSchreierMap.{u, v} X hp hX).hom)
      (toSheafify_zmodSheafHom.{u, v} X hX))
    (zmodPresheafHom_comp_artinSchreierMap X hp hX)

include hp in
/-- **Two distinct residue classes give the same function only on a scheme with no points**: if
they do, the ring of global functions is zero. -/
theorem zero_eq_one_of_constZModHom_eq (U : X.Etale) {a b : ZMod p} (hab : a ≠ b)
    (h : constZModHom X hX U a = constZModHom X hX U b) : (0 : Γ(U.left, ⊤)) = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hz : a - b ≠ 0 := sub_ne_zero.mpr hab
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k • (a - b) = 1 :=
    ⟨((a - b)⁻¹).val, by rw [nsmul_eq_mul, ZMod.natCast_val, ZMod.cast_id, inv_mul_cancel₀ hz]⟩
  calc (0 : Γ(U.left, ⊤)) = k • constZModHom X hX U (a - b) := by
        rw [map_sub, h, sub_self]
        exact (smul_zero k).symm
    _ = constZModHom X hX U (k • (a - b)) := (map_nsmul _ _ _).symm
    _ = 1 := by rw [hk, constZModHom_one]

include hp in
/-- The constant presheaf map is locally injective. -/
theorem isLocallyInjective_zmodPresheafHom :
    Presheaf.IsLocallyInjective X.smallEtaleTopology (zmodPresheafHom.{u, v} X hX) := by
  refine ⟨fun {U} a b h => ?_⟩
  by_cases hab : a = b
  · subst hab
    exact X.smallEtaleTopology.superset_covering (fun V g _ => rfl)
      (X.smallEtaleTopology.top_mem U.unop)
  · exact mem_smallEtaleTopology_of_isEmpty X U.unop
      (isEmpty_of_zero_eq_one _ (zero_eq_one_of_constZModHom_eq X hp hX U.unop
        (fun hd => hab (ULift.ext _ _ hd)) (congrArg ULift.down h))) _

include hp in
/-- The inclusion `𝐙/p𝐙 ⟶ 𝐆_a` is locally injective. -/
theorem isLocallyInjective_zmodSheafHom_hom :
    Presheaf.IsLocallyInjective X.smallEtaleTopology (zmodSheafHom.{u, v} X hX).hom := by
  have h := isLocallyInjective_zmodPresheafHom.{u, v} X hp hX
  rw [← toSheafify_zmodSheafHom.{u, v} X hX] at h
  exact (Presheaf.comp_isLocallyInjective_iff X.smallEtaleTopology
    (toSheafify X.smallEtaleTopology
      ((Functor.const X.Etaleᵒᵖ).obj
        (AddCommGrpCat.of (ULift.{max (u + 1) v} (ZMod p)))))
    (zmodSheafHom.{u, v} X hX).hom).1 h

/-- Sections of the kernel of the Artin–Schreier map inject into global functions. -/
theorem injective_kernel_ι_app (V : X.Etaleᵒᵖ) :
    Function.Injective ((kernel.ι (artinSchreierMap.{u, v} X hp hX)).hom.app V) :=
  (AddCommGrpCat.mono_iff_injective _).1
    ((NatTrans.mono_iff_mono_app _).1
      (Functor.map_mono (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) _) V)

/-- A section of the kernel of the Artin–Schreier map is a global function fixed by Frobenius. -/
theorem pow_eq_of_kernel (U : X.Etale)
    (s : ToType ((kernel (artinSchreierMap.{u, v} X hp hX)).obj.obj (op U)))
    (x : Γ(U.left, ⊤))
    (hx : (kernel.ι (artinSchreierMap.{u, v} X hp hX)).hom.app (op U) s = ofSection.{u, v} x) :
    x ^ p = x := by
  have h := congrArg
    (fun (ψ : kernel (artinSchreierMap.{u, v} X hp hX) ⟶ additiveSheaf.{u, v} X) =>
      ψ.hom.app (op U) s) (kernel.condition (artinSchreierMap.{u, v} X hp hX))
  simp only at h
  rw [show ((kernel.ι (artinSchreierMap.{u, v} X hp hX) ≫
      artinSchreierMap.{u, v} X hp hX).hom.app (op U)) s =
        (artinSchreierMap.{u, v} X hp hX).hom.app (op U)
          ((kernel.ι (artinSchreierMap.{u, v} X hp hX)).hom.app (op U) s) from rfl,
    hx, artinSchreierMap_app_ofSection] at h
  exact sub_eq_zero.mp (ofSection_injective.{u, v} (h.trans ofSection_zero.symm))

include hp in
/-- The comparison from the constant sheaf `𝐙/p𝐙` into the kernel of the Artin–Schreier map. -/
def artinSchreierKernelLift :
    (constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj
        (AddCommGrpCat.of (ULift.{max (u + 1) v} (ZMod p))) ⟶
      kernel (artinSchreierMap.{u, v} X hp hX) :=
  kernel.lift _ (zmodSheafHom.{u, v} X hX) (zmodSheafHom_comp_artinSchreierMap X hp hX)

/-- The comparison `artinSchreierKernelLift` followed by the kernel inclusion is
`zmodSheafHom`. -/
theorem artinSchreierKernelLift_comp_ι :
    artinSchreierKernelLift.{u, v} X hp hX ≫ kernel.ι (artinSchreierMap.{u, v} X hp hX) =
      zmodSheafHom.{u, v} X hX :=
  kernel.lift_ι _ _ _

/-- On sections, the comparison into the kernel followed by the kernel inclusion is
`zmodSheafHom`. -/
private theorem kernel_ι_lift_app (U : X.Etaleᵒᵖ)
    (a : ToType (((constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj
      (AddCommGrpCat.of (ULift.{max (u + 1) v} (ZMod p)))).obj.obj U)) :
    (kernel.ι (artinSchreierMap.{u, v} X hp hX)).hom.app U
      ((artinSchreierKernelLift.{u, v} X hp hX).hom.app U a) =
        (zmodSheafHom.{u, v} X hX).hom.app U a :=
  ConcreteCategory.congr_hom (NatTrans.congr_app
    (congrArg (·.hom) (artinSchreierKernelLift_comp_ι.{u, v} X hp hX)) U) a

/-- **The comparison into the kernel is locally surjective.** -/
theorem isLocallySurjective_artinSchreierKernelLift :
    Sheaf.IsLocallySurjective (artinSchreierKernelLift.{u, v} X hp hX) := by
  refine ⟨fun {U} s => ?_⟩
  obtain ⟨x, hx⟩ := ofSection_surjective.{u, v}
    ((kernel.ι (artinSchreierMap.{u, v} X hp hX)).hom.app (op U) s)
  have hxp : x ^ p = x := pow_eq_of_kernel X hp hX U s x hx.symm
  choose W g hg i ht hval using fun t : U.left =>
    exists_etale_natCast_of_point X hp hX U x hxp t
  have hetale (t : U.left) : Etale (g t ≫ U.hom) := by
    have := hg t
    infer_instance
  let Z : U.left → X.Etale := fun t => Scheme.Etale.mk (g t ≫ U.hom)
  let f : (t : U.left) → Z t ⟶ U := fun t => MorphismProperty.Over.homMk (g t) rfl
  have hleft (t : U.left) : (f t).left = g t := rfl
  have hcov : Sieve.ofArrows Z f ∈ X.smallEtaleTopology U := by
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    exact Set.eq_univ_of_forall fun t => Set.mem_iUnion.2 ⟨t, ht t⟩
  refine X.smallEtaleTopology.superset_covering ?_ hcov
  rw [Sieve.ofArrows, Sieve.generate_le_iff]
  rintro V - ⟨t⟩
  refine ⟨(toSheafify X.smallEtaleTopology
    ((Functor.const X.Etaleᵒᵖ).obj
      (AddCommGrpCat.of (ULift.{max (u + 1) v} (ZMod p))))).app (op (Z t))
        (ULift.up (((i t : ℕ) : ZMod p))), ?_⟩
  refine injective_kernel_ι_app X hp hX (op (Z t)) ?_
  have hL : (kernel.ι (artinSchreierMap.{u, v} X hp hX)).hom.app (op (Z t))
      ((artinSchreierKernelLift.{u, v} X hp hX).hom.app (op (Z t))
        ((toSheafify X.smallEtaleTopology
          ((Functor.const X.Etaleᵒᵖ).obj
            (AddCommGrpCat.of (ULift.{max (u + 1) v} (ZMod p))))).app (op (Z t))
              (ULift.up (((i t : ℕ) : ZMod p))))) =
      ofSection.{u, v} ((i t : ℕ) : Γ((Z t).left, ⊤)) := by
    rw [← constZModHom_natCast X hX (Z t) (i t)]
    exact (kernel_ι_lift_app X hp hX _ _).trans
      (ConcreteCategory.congr_hom (NatTrans.congr_app (toSheafify_zmodSheafHom.{u, v} X hX)
        (op (Z t))) (ULift.up (((i t : ℕ) : ZMod p))))
  rw [hL, NatTrans.naturality_apply
    (kernel.ι (artinSchreierMap.{u, v} X hp hX)).hom (f t).op s, ← hx, map_ofSection, hleft t]
  exact congrArg _ (hval t).symm

/-- The comparison into the kernel is locally injective. -/
theorem isLocallyInjective_artinSchreierKernelLift :
    Sheaf.IsLocallyInjective (artinSchreierKernelLift.{u, v} X hp hX) := by
  refine ⟨fun {U} a b h => ?_⟩
  refine (isLocallyInjective_zmodSheafHom_hom.{u, v} X hp hX).equalizerSieve_mem a b ?_
  exact (kernel_ι_lift_app X hp hX U a).symm.trans
    ((congrArg ((kernel.ι (artinSchreierMap.{u, v} X hp hX)).hom.app U) h).trans
      (kernel_ι_lift_app X hp hX U b))

/-- **The Artin–Schreier sequence** `𝐙/p𝐙 ⟶ 𝐆_a ⟶ 𝐆_a` on the small étale site of a scheme of
characteristic `p`, the second map being `x ↦ x ^ p - x` and the first the inclusion of the
constant sheaf as the scalar functions. -/
def constantArtinSchreierSequence :
    ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :=
  ShortComplex.mk (zmodSheafHom.{u, v} X hX) (artinSchreierMap.{u, v} X hp hX)
    (zmodSheafHom_comp_artinSchreierMap X hp hX)

/-- **The Artin–Schreier sequence.** For a scheme `X` of characteristic `p`,

`0 ⟶ 𝐙/p𝐙 ⟶ 𝐆_a ⟶ 𝐆_a ⟶ 0`

is a short exact sequence of abelian sheaves on the small étale site of `X`, the second map being
`x ↦ x ^ p - x`. -/
@[stacks 0A3J, sga "1 XI 6.7", sga "4 IX 3.5"]
theorem constantArtinSchreierSequence_shortExact :
    (constantArtinSchreierSequence.{u, v} X hp hX).ShortExact := by
  have hli := isLocallyInjective_zmodSheafHom_hom.{u, v} X hp hX
  have hsurj := isLocallySurjective_artinSchreierKernelLift.{u, v} X hp hX
  have hmono : Mono (zmodSheafHom.{u, v} X hX) :=
    Sheaf.mono_of_isLocallyInjective (zmodSheafHom.{u, v} X hX)
  refine ShortComplex.ShortExact.mk' ?_ hmono (epi_artinSchreierMap.{u, v} X hp hX)
  rw [ShortComplex.exact_iff_epi_kernel_lift]
  exact Sheaf.epi_of_isLocallySurjective (artinSchreierKernelLift.{u, v} X hp hX)

end Comparison

end Stacks.ArtinSchreier

end
