module

public import Mathlib.RingTheory.Noetherian.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafIsoDescent
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.QuotientByIdeal
public import StacksFrontier.AlgebraicGeometry.ProEtale.Constructible.AdicModuleSheaf
public import StacksFrontier.AlgebraicGeometry.ProEtale.Constructible.ConstantAdicReductions
public import StacksFrontier.AlgebraicGeometry.ProEtale.ExtensionByZero.AdicSheaves
public import StacksFrontier.CategoryTheory.MittagLefflerSections
public import StacksFrontier.RingTheory.AdicCompletion.InverseLimit
public import StacksFrontier.RingTheory.Module.FiniteFromAdicReduction
public import StacksCore.Tactic.StacksAttribute

/-!
# Sheaves of modules with constant adic reductions, on a site with a terminal object

Let `Λ` be a Noetherian ring, `I ⊆ Λ` an ideal and `F` a sheaf of `Λ`-modules on a site with a
terminal object, for instance the small pro-étale site of a scheme or a slice of it. If every
reduction `F / IⁿF` is a constant sheaf and the first one is the constant sheaf of a finite module,
then there is a single `I`-adically complete `Λ`-module `M`, finite over `Λ^∧`, whose own
reductions `M / IⁿM` have the reductions of `F` as their constant sheaves: the tower of constant
sheaves whose limit is the completed constant sheaf of `M` is termwise isomorphic to the adic
quotient tower of `F`.

This file states, for an arbitrary site with a terminal object, what
`StacksFrontier/AlgebraicGeometry/ProEtale/Constructible/ConstantAdicReductions.lean` states for the
small pro-étale site of a scheme, with the quotient characterized by
`Stacks.ModuleSheaf.IsQuotientBy`. The statements about the adic quotient tower of a module alone
(`AlgebraicGeometry.ProEtale.adicQuotientCone`,
`AlgebraicGeometry.ProEtale.surjective_adicQuotient_transitionMap`) do not involve the site and
are used from there.

## Main definitions

* `Stacks.ModuleSheaf.constantSheafAdjTerminal`: the constant-sheaf adjunction on a site with a
  terminal object, with global sections taken over the terminal object.
* `Stacks.ModuleSheaf.constantAdicQuotientTower`: the tower `n ↦ (M / IⁿM)̲` of constant
  sheaves of the adic quotients of a module, whose limit is the completed constant sheaf of `M`.
* `Stacks.ModuleSheaf.constantAdicQuotientCone`: the cone of quotient maps `M̲ ⟶ (M / IⁿM)̲`
  over that tower.

## Main results

* `Stacks.ModuleSheaf.isAnnihilatedBy_constantSheaf`: the constant sheaf of a module
  annihilated by an ideal is annihilated by that ideal.
* `Stacks.ModuleSheaf.isQuotientBy_constantSheaf`: the constant sheaf of the reduction
  `A ⧸ JA` is the quotient of `A̲` by `J`.
* `Stacks.ModuleSheaf.smul_top_eq_bot_of_constantSheaf_iso`: an ideal annihilating a
  sheaf annihilates the value of a constant sheaf isomorphic to it.
* `Stacks.ModuleSheaf.exists_isAdicComplete_constantSheaf_iso_of_isConstant`: an
  `I`-adically complete module whose tower of constant reductions is termwise isomorphic to the
  adic quotient tower of `F`, from finiteness of the value at every level.
* `Stacks.ModuleSheaf.exists_finite_constantSheaf_iso_of_isConstant`: finiteness of the
  value at level one propagates to every level.
* `Stacks.ModuleSheaf.exists_finite_isAdicComplete_constantSheaf_iso_of_isConstant`:
  the two combined, under the hypotheses of Tag 09BV, with `M` finite over `Λ^∧`.
* `Stacks.ModuleSheaf.epi_constantSheaf_map`: the constant sheaf functor preserves
  epimorphisms.
* `Stacks.ModuleSheaf.isQuotientBy_constantAdicQuotientTower_map`: every transition map
  of `constantAdicQuotientTower` exhibits its target as the quotient of its source by the
  relevant power of `I`.
* `Stacks.ModuleSheaf.epi_constantAdicQuotientTower_map`: those transition maps are
  epimorphisms.
* `Stacks.ModuleSheaf.descendsIsos_constantAdicQuotientTower_self` and
  `Stacks.ModuleSheaf.descendsIsos_constantAdicQuotientTower`: isomorphisms descend
  along those transition maps, to the tower itself and to the adic quotient tower of `F`.

## Implementation notes

The statements are made for an arbitrary site with a terminal object, so that they apply to the
slices of the small pro-étale site over its objects as well as to the site itself; the instance
`HasTerminal X.ProEt` comes from `AlgebraicGeometry.ProEtale.isTerminalProEtId`.

The adic quotient tower of `F` is not constructed but characterized, by
`Stacks.ModuleSheaf.IsQuotientBy`: its `n`-th term is required to be initial among
morphisms out of `F` to sheaves annihilated by `Iⁿ`. This pins down the actual quotients
`F / IⁿF` and their canonical transition maps up to unique isomorphism.
`isQuotientBy_constantSheaf` transports that characterization from sheaves to modules: it is
proved from the constant-sheaf adjunction at the terminal object of the site, where the
universal property of the quotient module is available, rather than from any construction of
the quotient sheaf.

The descent for morphisms of constant sheaves
(`Stacks.ConstantSheaf.exists_surjective_ker_eq_of_constantSheaf_quotient_iso`) consumes
finiteness of the value at every level, which is more than the source assumes; the source asks
only that `F / IF` be of finite type, equivalently — by Tag 093N (1), for a constant sheaf —
that the value at level one be finite. `exists_finite_constantSheaf_iso_of_isConstant` closes the
difference: `Iⁿ` annihilates the value `N` at level `n`, the reduction `N ⧸ IN` is a quotient of
the value at level one by the asymmetric descent
`Stacks.ConstantSheaf.exists_surjective_of_constantSheaf_iso`, and `N` is then finite by Nakayama
for a nilpotently acting ideal.

Non-emptiness of the topos is hypothesized, as the descent for constant sheaves needs it. The
compatible choice of the termwise isomorphisms, which identifies `F` with the completed constant
sheaf of `M`, is in
`StacksFrontier/AlgebraicGeometry/ProEtale/Constructible/ConstantAdicQuotientTowerIso.lean`.

## References

* [Stacks Project, Tag 09BV](https://stacks.math.columbia.edu/tag/09BV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w r

namespace AlgebraicGeometry.ProEtale

/-- The small pro-étale site of `X` has a terminal object, the identity of `X`. -/
instance (X : Scheme.{u}) : HasTerminal X.ProEt := (isTerminalProEtId X).hasTerminal

end AlgebraicGeometry.ProEtale

namespace Stacks.ModuleSheaf

open AlgebraicGeometry.ProEtale (adicQuotientModuleSystem adicQuotientCone
  surjective_adicQuotient_transitionMap)

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) [HasTerminal C]
  (Λ : Type r) [CommRing Λ]

section Annihilated

variable [HasWeakSheafify J (ModuleCat.{w} Λ)]
  [J.WEqualsLocallyBijective (ModuleCat.{w} Λ)]
  [J.HasSheafCompose (forget (ModuleCat.{w} Λ))]

omit [HasTerminal C] in
/-- The constant sheaf of a module annihilated by an ideal is annihilated by that ideal. -/
theorem isAnnihilatedBy_constantSheaf (K : Ideal Λ) (B : ModuleCat.{w} Λ)
    (hB : ∀ a ∈ K, ∀ b : B, a • b = 0) :
    IsAnnihilatedBy J Λ K
      ((constantSheaf J (ModuleCat.{w} Λ)).obj B) := by
  intro U a ha x
  refine ((constantSheaf J (ModuleCat.{w} Λ)).obj B).property.isSeparated
    _ _ (Presheaf.imageSieve_mem J
      (toSheafify J ((Functor.const Cᵒᵖ).obj B)) x) _ _ ?_
  rintro Y q ⟨m, hm⟩
  have h2 : (((constantSheaf J (ModuleCat.{w} Λ)).obj B).obj.map q.op).hom x
      = (Stacks.ConstantSheaf.constantUnitApp J B (op Y)).hom m := hm.symm
  rw [map_zero, map_smul, h2, ← map_smul, show a • m = 0 from hB a ha m, map_zero]

omit [HasTerminal C] [J.HasSheafCompose (forget (ModuleCat.{w} Λ))] in
/-- An ideal annihilating a sheaf annihilates the value of a constant sheaf isomorphic to it,
as soon as some object of the site is not sheaf theoretically empty. -/
theorem smul_top_eq_bot_of_constantSheaf_iso (K : Ideal Λ)
    (hne : ∃ U : C, (⊥ : Sieve U) ∉ J U) (N : ModuleCat.{w} Λ)
    {H : Sheaf J (ModuleCat.{w} Λ)} (hH : IsAnnihilatedBy J Λ K H)
    (e : (constantSheaf J (ModuleCat.{w} Λ)).obj N ≅ H) :
    K • (⊤ : Submodule Λ (N : Type w)) = ⊥ := by
  obtain ⟨U, hU⟩ := hne
  have hLI : ∀ y, (e.inv.hom.app (op U)).hom ((e.hom.hom.app (op U)).hom y) = y := fun y => by
    change ((e.hom ≫ e.inv).hom.app (op U)).hom y = y
    rw [e.hom_inv_id]
    rfl
  have hinj : Function.Injective (e.hom.hom.app (op U)).hom :=
    Function.LeftInverse.injective hLI
  refine le_antisymm (Submodule.smul_le.2 fun a ha m _ => ?_) bot_le
  refine (Submodule.mem_bot _).2
    (Stacks.ConstantSheaf.injective_constantUnitApp J N hU (hinj ?_))
  have h1 : (Stacks.ConstantSheaf.constantUnitApp J N (op U)).hom (a • m) =
      a • (Stacks.ConstantSheaf.constantUnitApp J N (op U)).hom m :=
    map_smul _ a m
  rw [h1, map_smul, map_zero, map_zero]
  exact hH U a ha _

/-- The constant-sheaf adjunction on the small pro-étale site, with global sections taken over
the identity of `X`. -/
abbrev constantSheafAdjTerminal :
    constantSheaf J (ModuleCat.{w} Λ) ⊣
      (sheafSections J (ModuleCat.{w} Λ)).obj
        (op (⊤_ C)) :=
  constantSheafAdj _ _ terminalIsTerminal

omit [J.WEqualsLocallyBijective (ModuleCat.{w} Λ)]
  [J.HasSheafCompose (forget (ModuleCat.{w} Λ))] in
/-- Morphisms out of the constant sheaf of a quotient module are determined by their
composition with the constant sheaf of the quotient map. -/
theorem constantSheaf_quotient_hom_ext {A : ModuleCat.{w} Λ} (P : Submodule Λ A)
    {H : Sheaf J (ModuleCat.{w} Λ)}
    (φ φ' : (constantSheaf J (ModuleCat.{w} Λ)).obj
        (ModuleCat.of Λ (A ⧸ P)) ⟶ H)
    (h : (constantSheaf J (ModuleCat.{w} Λ)).map
          (ModuleCat.ofHom P.mkQ) ≫ φ =
        (constantSheaf J (ModuleCat.{w} Λ)).map
          (ModuleCat.ofHom P.mkQ) ≫ φ') :
    φ = φ' := by
  have hepi : Epi (ModuleCat.ofHom P.mkQ) :=
    (ModuleCat.epi_iff_surjective _).2 P.mkQ_surjective
  refine (constantSheafAdjTerminal J Λ).homEquiv _ H |>.injective ?_
  have h1 := (constantSheafAdjTerminal J Λ).homEquiv_naturality_left (ModuleCat.ofHom P.mkQ) φ
  have h2 := (constantSheafAdjTerminal J Λ).homEquiv_naturality_left (ModuleCat.ofHom P.mkQ) φ'
  exact (cancel_epi (ModuleCat.ofHom P.mkQ)).1 (h1.symm.trans ((congrArg _ h).trans h2))

/-- The constant sheaf of the reduction `A ⧸ K A` is the quotient of the constant sheaf of `A`
by the ideal `K`: it is annihilated by `K` and initial among morphisms out of `A̲` to sheaves
annihilated by `K`. -/
theorem isQuotientBy_constantSheaf (K : Ideal Λ) (A : ModuleCat.{w} Λ) :
    IsQuotientBy J Λ K
      ((constantSheaf J (ModuleCat.{w} Λ)).obj A)
      ((constantSheaf J (ModuleCat.{w} Λ)).obj
        (ModuleCat.of Λ (A ⧸ (K • ⊤ : Submodule Λ A))))
      ((constantSheaf J (ModuleCat.{w} Λ)).map
        (ModuleCat.ofHom (K • (⊤ : Submodule Λ A)).mkQ)) := by
  refine ⟨isAnnihilatedBy_constantSheaf J Λ K _ ?_, ?_⟩
  · intro a ha b
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    exact (Submodule.Quotient.mk_eq_zero _).2
      (Submodule.smul_mem_smul ha Submodule.mem_top)
  · intro H hH f
    refine ⟨?_, ?_, fun g hg => constantSheaf_quotient_hom_ext J Λ _ _ _ (hg.trans ?_)⟩
    · exact ((constantSheafAdjTerminal J Λ).homEquiv _ H).symm
        (ModuleCat.ofHom ((K • (⊤ : Submodule Λ A)).liftQ
          (((constantSheafAdjTerminal J Λ).homEquiv A H) f).hom (by
            refine Submodule.smul_le.2 fun r hr n _ => ?_
            simp only [LinearMap.mem_ker, map_smul]
            exact hH (⊤_ C) r hr _)))
    all_goals
      refine ((constantSheafAdjTerminal J Λ).homEquiv A H).injective ?_
      rw [(constantSheafAdjTerminal J Λ).homEquiv_naturality_left, Equiv.apply_symm_apply]
      first
        | exact ModuleCat.hom_ext (Submodule.liftQ_mkQ _ _ _)
        | exact (ModuleCat.hom_ext (Submodule.liftQ_mkQ _ _ _)).symm

end Annihilated


section Main

variable [IsNoetherianRing Λ]
  [HasSheafify J (ModuleCat.{w} Λ)]
  [J.WEqualsLocallyBijective (ModuleCat.{w} Λ)]
  [J.HasSheafCompose (forget (ModuleCat.{w} Λ))]

/-- If every reduction `F / IⁿF` of a sheaf of `Λ`-modules on the small pro-étale site is the
constant sheaf of a finite `Λ`-module, then there is an `I`-adically complete `Λ`-module `M`,
with every reduction `M / IⁿM` finite over `Λ`, whose tower of constant reductions — the tower
whose limit is the completed constant sheaf of `M` — is termwise isomorphic to the adic quotient
tower of `F`.

The hypothesis is stronger than the source's, which asks finite type of `F / IF` alone;
`exists_finite_isAdicComplete_constantSheaf_iso_of_isConstant` is the same statement under the
source's hypotheses and is the declaration that carries the attribute. -/
theorem exists_isAdicComplete_constantSheaf_iso_of_isConstant (I : Ideal Λ)
    (hne : ∃ U : C, (⊥ : Sieve U) ∉ J U)
    (F : Sheaf J (ModuleCat.{w} Λ))
    (Q : ℕᵒᵖ ⥤ Sheaf J (ModuleCat.{w} Λ))
    (q : (Functor.const ℕᵒᵖ).obj F ⟶ Q)
    (hq : ∀ n : ℕ, IsQuotientBy J Λ (I ^ n) F (Q.obj (op n)) (q.app (op n)))
    (hconst : ∀ n : ℕ, ∃ N : ModuleCat.{w} Λ, Module.Finite Λ (N : Type w) ∧
      Nonempty ((constantSheaf J (ModuleCat.{w} Λ)).obj N ≅
        Q.obj (op n))) :
    ∃ M : ModuleCat.{w} Λ, IsAdicComplete I (M : Type w) ∧
      Module.Finite Λ ((M : Type w) ⧸ (I • ⊤ : Submodule Λ (M : Type w))) ∧
      (∀ n : ℕ, Module.Finite Λ ((M : Type w) ⧸ (I ^ n • ⊤ : Submodule Λ (M : Type w)))) ∧
      ∀ n : ℕ, Nonempty ((adicQuotientModuleSystem Λ I M ⋙
        constantSheaf J (ModuleCat.{w} Λ)).obj (op n) ≅
          Q.obj (op n)) := by
  classical
  have hIFG : I.FG := IsNoetherian.noetherian I
  choose N hNfin hNiso using hconst
  -- the chosen isomorphisms `N n̲ ≅ F / IⁿF`
  set e : ∀ n : ℕ, (constantSheaf J (ModuleCat.{w} Λ)).obj (N n) ≅
      Q.obj (op n) := fun n => (hNiso n).some with he
  -- the reduction of `N (n+1)` modulo `Iⁿ` is the `n`-th term of the tower
  have key : ∀ n : ℕ,
      (constantSheaf J (ModuleCat.{w} Λ)).obj
          (ModuleCat.of Λ ((N (n + 1) : Type w) ⧸
            (I ^ n • ⊤ : Submodule Λ (N (n + 1) : Type w)))) ≅
        (constantSheaf J (ModuleCat.{w} Λ)).obj (N n) := fun n =>
    isQuotientByIso (isQuotientBy_constantSheaf J Λ (I ^ n) (N (n + 1)))
        (isQuotientBy_of_iso (e (n + 1))
          (isQuotientBy_map_of_tower I q hq (Nat.le_succ n))) ≪≫ (e n).symm
  -- descend to surjections of modules with the prescribed kernels
  have hψ : ∀ n : ℕ, ∃ ψ : N (n + 1) ⟶ N n, Function.Surjective ψ.hom ∧
      LinearMap.ker ψ.hom = (I ^ n • ⊤ : Submodule Λ (N (n + 1) : Type w)) := by
    intro n
    have := hNfin (n + 1)
    have := hNfin n
    have : Module.Finite Λ ((N (n + 1) : Type w) ⧸
        (I ^ n • ⊤ : Submodule Λ (N (n + 1) : Type w))) := Module.Finite.quotient _ _
    have := Module.finitePresentation_of_finite Λ ((N (n + 1) : Type w) ⧸
      (I ^ n • ⊤ : Submodule Λ (N (n + 1) : Type w)))
    have := Module.finitePresentation_of_finite Λ (N n : Type w)
    exact Stacks.ConstantSheaf.exists_surjective_ker_eq_of_constantSheaf_quotient_iso
      J hne (N (n + 1)) (N n) _ (key n)
  choose ψ hψsurj hψker using hψ
  -- the resulting inverse system and its limit
  let S : Stacks.AdicCompletion.InverseLimit.InverseSystem I :=
    { M := fun n => (N n : Type w)
      π := fun n => (ψ n).hom
      surjective := hψsurj
      ker_π := hψker }
  refine ⟨ModuleCat.of Λ S.limit, S.isAdicComplete hIFG, ?_, fun n => ?_, fun n => ?_⟩
  · have := hNfin 1
    exact Module.Finite.equiv
      ((Submodule.quotEquivOfEq _ _ (by rw [pow_one])).trans (S.quotientEquiv hIFG 1)).symm
  · have := hNfin n
    exact Module.Finite.equiv (S.quotientEquiv hIFG n).symm
  · exact ⟨(constantSheaf J (ModuleCat.{w} Λ)).mapIso
      (LinearEquiv.toModuleIso (S.quotientEquiv hIFG n)) ≪≫ e n⟩

/-- If every reduction `F / IⁿF` of a sheaf of `Λ`-modules is a constant sheaf and `F / IF` is
the constant sheaf of a finite module, then every reduction is the constant sheaf of a finite
module: `Iⁿ` annihilates the value at level `n`, whose reduction modulo `I` is a quotient of the
value at level one, so Nakayama applies. -/
theorem exists_finite_constantSheaf_iso_of_isConstant (I : Ideal Λ)
    (hne : ∃ U : C, (⊥ : Sieve U) ∉ J U)
    (F : Sheaf J (ModuleCat.{w} Λ))
    (Q : ℕᵒᵖ ⥤ Sheaf J (ModuleCat.{w} Λ))
    (q : (Functor.const ℕᵒᵖ).obj F ⟶ Q)
    (hq : ∀ n : ℕ, IsQuotientBy J Λ (I ^ n) F (Q.obj (op n)) (q.app (op n)))
    (hconst : ∀ n : ℕ, ∃ N : ModuleCat.{w} Λ,
      Nonempty ((constantSheaf J (ModuleCat.{w} Λ)).obj N ≅
        Q.obj (op n)))
    (hfin : ∃ N : ModuleCat.{w} Λ, Module.Finite Λ (N : Type w) ∧
      Nonempty ((constantSheaf J (ModuleCat.{w} Λ)).obj N ≅
        Q.obj (op 1)))
    (n : ℕ) :
    ∃ N : ModuleCat.{w} Λ, Module.Finite Λ (N : Type w) ∧
      Nonempty ((constantSheaf J (ModuleCat.{w} Λ)).obj N ≅
        Q.obj (op n)) := by
  obtain ⟨N, ⟨e⟩⟩ := hconst n
  obtain ⟨N₁, hN₁fin, ⟨e₁⟩⟩ := hfin
  refine ⟨N, ?_, ⟨e⟩⟩
  have hnil : I ^ n • (⊤ : Submodule Λ (N : Type w)) = ⊥ :=
    smul_top_eq_bot_of_constantSheaf_iso J Λ (I ^ n) hne N (hq n).1 e
  have hred : Module.Finite Λ ((N : Type w) ⧸ (I • ⊤ : Submodule Λ (N : Type w))) := by
    match n, e, hnil with
    | 0, _, hnil =>
      rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul] at hnil
      have : Module.Finite Λ (N : Type w) := Module.finite_def.mpr (hnil ▸ Submodule.fg_bot)
      exact Module.Finite.quotient _ _
    | (n' + 1), e, _ =>
      have h1n : 1 ≤ n' + 1 := Nat.le_add_left 1 n'
      have hcomp := isQuotientByIso (isQuotientBy_constantSheaf J Λ (I ^ 1) N)
        (isQuotientBy_of_iso e (isQuotientBy_map_of_tower I q hq h1n))
      have := Module.finitePresentation_of_finite Λ (N₁ : Type w)
      have hfin1 : Module.Finite Λ
          ((N : Type w) ⧸ (I ^ 1 • ⊤ : Submodule Λ (N : Type w))) :=
        Stacks.ConstantSheaf.finite_of_constantSheaf_iso J hne N₁ _
          (e₁ ≪≫ hcomp.symm)
      exact hfin1.equiv (Submodule.quotEquivOfEq _ _ (by rw [pow_one]))
  exact Module.Finite.of_pow_smul_top_eq_bot I (N : Type w) hnil hred

/-- **Stacks 09BV, the coefficient module, on a site with a terminal object.** Let `Λ` be
Noetherian, `I ⊆ Λ` an ideal and `F` a sheaf of `Λ`-modules on a site with a terminal object whose
topos is not empty, whose reductions `F / IⁿF` are constant sheaves and whose first reduction is
the constant sheaf of a finite module. Then there is an `I`-adically complete `Λ`-module `M`,
finite over `Λ^∧` and with every reduction `M / IⁿM` finite over `Λ`, whose tower of constant
reductions is termwise isomorphic to the adic quotient tower of `F`. -/
@[stacks 09BV "the coefficient module, on any site with a terminal object"]
theorem exists_finite_isAdicComplete_constantSheaf_iso_of_isConstant (I : Ideal Λ)
    (hne : ∃ U : C, (⊥ : Sieve U) ∉ J U)
    (F : Sheaf J (ModuleCat.{w} Λ))
    (Q : ℕᵒᵖ ⥤ Sheaf J (ModuleCat.{w} Λ))
    (q : (Functor.const ℕᵒᵖ).obj F ⟶ Q)
    (hq : ∀ n : ℕ, IsQuotientBy J Λ (I ^ n) F (Q.obj (op n)) (q.app (op n)))
    (hconst : ∀ n : ℕ, ∃ N : ModuleCat.{w} Λ,
      Nonempty ((constantSheaf J (ModuleCat.{w} Λ)).obj N ≅
        Q.obj (op n)))
    (hfin : ∃ N : ModuleCat.{w} Λ, Module.Finite Λ (N : Type w) ∧
      Nonempty ((constantSheaf J (ModuleCat.{w} Λ)).obj N ≅
        Q.obj (op 1))) :
    ∃ M : ModuleCat.{w} Λ, IsAdicComplete I (M : Type w) ∧
      Module.Finite Λ ((M : Type w) ⧸ (I • ⊤ : Submodule Λ (M : Type w))) ∧
      Module.Finite (AdicCompletion I Λ) (AdicCompletion I (M : Type w)) ∧
      (∀ n : ℕ, Module.Finite Λ ((M : Type w) ⧸ (I ^ n • ⊤ : Submodule Λ (M : Type w)))) ∧
      ∀ n : ℕ, Nonempty ((adicQuotientModuleSystem Λ I M ⋙
        constantSheaf J (ModuleCat.{w} Λ)).obj (op n) ≅
          Q.obj (op n)) := by
  obtain ⟨M, hMcomplete, hMfin, hMfinpow, hMiso⟩ :=
    exists_isAdicComplete_constantSheaf_iso_of_isConstant J Λ I hne F Q q hq
      (exists_finite_constantSheaf_iso_of_isConstant J Λ I hne F Q q hq hconst hfin)
  exact ⟨M, hMcomplete, hMfin,
    Module.Finite.adicCompletion_of_finite_quotient_smul_top (IsNoetherian.noetherian I)
      (M : Type w) hMfin, hMfinpow, hMiso⟩

end Main

section Compatible

variable [HasWeakSheafify J (ModuleCat.{w} Λ)]
  [J.WEqualsLocallyBijective (ModuleCat.{w} Λ)]
  [J.HasSheafCompose (forget (ModuleCat.{w} Λ))]
  (I : Ideal Λ) (M : ModuleCat.{w} Λ)

omit [J.WEqualsLocallyBijective (ModuleCat.{w} Λ)]
  [J.HasSheafCompose (forget (ModuleCat.{w} Λ))] in
/-- The constant sheaf functor preserves epimorphisms, being a left adjoint. -/
theorem epi_constantSheaf_map {A B : ModuleCat.{w} Λ} (φ : A ⟶ B) [Epi φ] :
    Epi ((constantSheaf J (ModuleCat.{w} Λ)).map φ) :=
  ⟨fun {H} u v huv => ((constantSheafAdjTerminal J Λ).homEquiv _ H).injective
    ((cancel_epi φ).1 ((((constantSheafAdjTerminal J Λ).homEquiv_naturality_left φ u).symm.trans
      (congrArg _ huv)).trans ((constantSheafAdjTerminal J Λ).homEquiv_naturality_left φ v)))⟩

/-- The tower of constant sheaves of the adic quotients `M / IⁿM`, whose limit is the completed
constant sheaf of `M`. -/
abbrev constantAdicQuotientTower :
    ℕᵒᵖ ⥤ Sheaf J (ModuleCat.{w} Λ) :=
  adicQuotientModuleSystem Λ I M ⋙ constantSheaf J (ModuleCat.{w} Λ)

omit [J.WEqualsLocallyBijective (ModuleCat.{w} Λ)]
  [J.HasSheafCompose (forget (ModuleCat.{w} Λ))] in
/-- Every transition map of the tower of constant sheaves of the adic quotients of `M` is an
epimorphism. -/
theorem epi_constantAdicQuotientTower_map ⦃m n : ℕᵒᵖ⦄ (f : m ⟶ n) :
    Epi ((constantAdicQuotientTower J Λ I M).map f) := by
  refine Functor.epi_map_of_epi_succ (fun k => ?_) f
  have : Epi ((adicQuotientModuleSystem Λ I M).map (homOfLE (Nat.le_succ k)).op) :=
    (ModuleCat.epi_iff_surjective _).2 (surjective_adicQuotient_transitionMap Λ I M k)
  exact epi_constantSheaf_map J Λ
    ((adicQuotientModuleSystem Λ I M).map (homOfLE (Nat.le_succ k)).op)

/-- The cone of quotient maps `M̲ ⟶ (M / IⁿM)̲`. -/
def constantAdicQuotientCone :
    (Functor.const ℕᵒᵖ).obj
        ((constantSheaf J (ModuleCat.{w} Λ)).obj M) ⟶
      constantAdicQuotientTower J Λ I M :=
  NatTrans.ofOpSequence
    (fun n => (constantSheaf J (ModuleCat.{w} Λ)).map
      ((adicQuotientCone Λ I M).app (op n)))
    (fun n => by
      have hnat := (adicQuotientCone Λ I M).naturality (homOfLE (Nat.le_add_right n 1)).op
      simp only [Functor.const_obj_map] at hnat ⊢
      rw [show (constantAdicQuotientTower J Λ I M).map (homOfLE (Nat.le_add_right n 1)).op =
            (constantSheaf J (ModuleCat.{w} Λ)).map
              ((adicQuotientModuleSystem Λ I M).map (homOfLE (Nat.le_add_right n 1)).op) from rfl,
        ← CategoryTheory.Functor.map_comp, ← hnat, CategoryTheory.Functor.map_comp,
        CategoryTheory.Functor.map_id])

/-- In the tower of constant sheaves of the adic quotients of `M`, every transition map exhibits
its target as the quotient of its source by the relevant power of `I`: the cone of quotient maps
out of `M̲` realizes each term as a quotient of `M̲`, by `isQuotientBy_constantSheaf`, so
`isQuotientBy_map_of_tower` applies. -/
theorem isQuotientBy_constantAdicQuotientTower_map ⦃m n : ℕᵒᵖ⦄ (f : m ⟶ n) :
    IsQuotientBy J Λ (I ^ n.unop) ((constantAdicQuotientTower J Λ I M).obj m)
      ((constantAdicQuotientTower J Λ I M).obj n)
      ((constantAdicQuotientTower J Λ I M).map f) := by
  rw [show f = (homOfLE (leOfHom f.unop)).op from Subsingleton.elim _ _]
  exact isQuotientBy_map_of_tower I (constantAdicQuotientCone J Λ I M)
    (fun k => isQuotientBy_constantSheaf J Λ (I ^ k) M) (leOfHom f.unop)

omit [HasTerminal C] [HasWeakSheafify J (ModuleCat.{w} Λ)]
  [J.WEqualsLocallyBijective (ModuleCat.{w} Λ)] [J.HasSheafCompose (forget (ModuleCat.{w} Λ))] in
/-- Isomorphisms descend along the transition maps of two towers each of whose transition maps
exhibits its target as the quotient by the relevant power of `I`: the induced map of quotients is
the descent, and `isQuotientByIso_hom_comp` is the square it has to make commute. -/
theorem descendsIsos_of_isQuotientBy_map
    {A B : ℕᵒᵖ ⥤ Sheaf J (ModuleCat.{w} Λ)}
    (hA : ∀ ⦃m n : ℕᵒᵖ⦄ (f : m ⟶ n),
      IsQuotientBy J Λ (I ^ n.unop) (A.obj m) (A.obj n) (A.map f))
    (hB : ∀ ⦃m n : ℕᵒᵖ⦄ (f : m ⟶ n),
      IsQuotientBy J Λ (I ^ n.unop) (B.obj m) (B.obj n) (B.map f)) :
    Functor.DescendsIsos A B := by
  intro m n f α
  exact ⟨isQuotientByIso (hA f) (isQuotientBy_of_iso α (hB f)),
    isQuotientByIso_hom_comp (hA f) (isQuotientBy_of_iso α (hB f))⟩

/-- Isomorphisms descend along the transition maps of the tower of constant sheaves of the adic
quotients of `M`. -/
theorem descendsIsos_constantAdicQuotientTower_self :
    Functor.DescendsIsos (constantAdicQuotientTower J Λ I M)
      (constantAdicQuotientTower J Λ I M) :=
  descendsIsos_of_isQuotientBy_map J Λ I (isQuotientBy_constantAdicQuotientTower_map J Λ I M)
    (isQuotientBy_constantAdicQuotientTower_map J Λ I M)

/-- Isomorphisms descend from the tower of constant sheaves of the adic quotients of `M` to the
adic quotient tower of a sheaf `F`. -/
theorem descendsIsos_constantAdicQuotientTower
    (F : Sheaf J (ModuleCat.{w} Λ))
    (Q : ℕᵒᵖ ⥤ Sheaf J (ModuleCat.{w} Λ))
    (q : (Functor.const ℕᵒᵖ).obj F ⟶ Q)
    (hq : ∀ n : ℕ, IsQuotientBy J Λ (I ^ n) F (Q.obj (op n)) (q.app (op n))) :
    Functor.DescendsIsos (constantAdicQuotientTower J Λ I M) Q :=
  descendsIsos_of_isQuotientBy_map J Λ I (isQuotientBy_constantAdicQuotientTower_map J Λ I M)
    (fun {m n} f => by
      rw [show f = (homOfLE (leOfHom f.unop)).op from Subsingleton.elim _ _]
      exact isQuotientBy_map_of_tower I q hq (leOfHom f.unop))

end Compatible

end Stacks.ModuleSheaf

end
