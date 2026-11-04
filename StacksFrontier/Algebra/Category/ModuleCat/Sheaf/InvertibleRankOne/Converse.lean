module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationStalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkFreeCover
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Invertible
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleCompare
public import StacksCore.Tactic.StacksAttribute

/-!
# An invertible module on a space with local stalks is locally free of rank one

Let `(X, 𝒪_X)` be a ringed space all of whose stalks `𝒪_{X, x}` are local rings and let `L` be an
invertible sheaf of `𝒪_X`-modules. This file proves that `L` is finite locally free of rank one,
which is the converse clause of [Stacks, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M).

## The argument

Invertibility produces a sheaf of modules `N` and a trivialization `ψ : L ⊗_{𝒪_X} N ≅ 𝒪_X`
(Tag 0B8K, `Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit`). At a point `x` the
induced pairing of stalks `L_x ⊗_{𝒪_{X, x}} N_x ≃ 𝒪_{X, x}` is
`Stacks.SheafOfModules.stalkPairing`, built from the stalk of a tensor product (Tag 01CB). Two
purely algebraic facts about that pairing carry the whole proof.

First, writing `ψ⁻¹ 1` as a finite sum of pure tensors and using that `𝒪_{X, x}` is local, one
summand pairs to a *unit*, so after rescaling there are `m₀ ∈ L_x` and `n₀ ∈ N_x` with
`ψ_x (m₀ ⊗ n₀) = 1` (`exists_tmul_eq_one_of_isLocalRing`). This is where the local-ring
hypothesis is used, and it is used nowhere else: without it the unit ideal can be a sum of
non-units and no single pure tensor need trivialize the pairing. Second, once such a pair exists,
`a ↦ a • m₀` is a *bijection* `𝒪_{X, x} → L_x` (`bijective_smul_of_tmul_eq_one`): contraction
against `n₀` is a left inverse, and over an invertible module a one-sided inverse is two-sided
(`Module.Invertible.rightInverse_of_leftInverse`).

Spreading out, `m₀` and `n₀` are germs of sections `s` of `L` and `b` of `N` over some
neighbourhood `U` of `x` with `ψ (s ⊗ b) = 1` in `𝒪_X(U)` (`exists_tensorPairing_eq_one_nhds`).
That identity restricts, so the bijectivity above holds at *every* point of `U`, not just at `x`.
Injectivity of `c ↦ c • s` on the sections over each `V ≤ U` then follows because a section of a
sheaf whose germs all vanish vanishes, and surjectivity up to shrinking follows because every
germ of `L` at a point of `V` is a multiple of the germ of `s`. These are exactly the two
hypotheses of `Stacks.SheafOfModules.nonempty_over_iso_free_of_inj_of_surj`, so `L` is free of
rank one on `U`.

Note what this route does **not** need: the finite presentation of `L` that the source's proof
takes from Tag 0B8K, and hence neither Tag 0B8J nor the clause of Tag 0B8K asserting that an
invertible module is locally a direct summand of a finite free module. Trivializing `L` on `U`
replaces spreading out a free stalk, because the stalk hypothesis is available at every point of
`U` at once rather than at a single point.

## Main results

* `Stacks.SheafOfModules.exists_tmul_eq_one_of_isLocalRing` and
  `Stacks.SheafOfModules.bijective_smul_of_tmul_eq_one`: the two algebraic facts above, for a
  module over a commutative ring.
* `Stacks.SheafOfModules.exists_tensorPairing_eq_one_nhds`: sections of `L` and of `N` pairing
  to the unit section on a neighbourhood of a given point.
* `Stacks.SheafOfModules.bijective_smul_grpGerm_of_tensorPairing_eq_one`: at every point of that
  neighbourhood, multiplication by the germ of `s` is a bijection from the stalk of the structure
  sheaf onto the stalk of `L`.
* `Stacks.SheafOfModules.nonempty_over_iso_unit_of_tensorPairing_eq_one`: the restriction of `L`
  to that neighbourhood is isomorphic to the structure sheaf.
* `Stacks.SheafOfModules.Invertible.isLocallyTrivial_of_isInvertible`: an invertible sheaf of
  modules on a ringed space with local stalks is locally trivial.
* `Stacks.SheafOfModules.Invertible.isFiniteLocallyFreeOfRank_one_of_isInvertible`: **the
  converse clause of Tag 0B8M.** Such a sheaf of modules is finite locally free of rank one.
* `Stacks.SheafOfModules.Invertible` also carries
  `isFiniteLocallyFreeOfRank_one_of_isInvertible_algebraicGeometry`: the same conclusion from the
  other spelling of invertibility in this library, obtained through
  `Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry`.

## Implementation notes

Two module structures on the stalk of a sheaf of modules occur in the library: the one of
[Stacks, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
(`Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule`), over the `CommRingCat`-valued stalk
  `Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk X x = 𝒪_{X, x}`, and Mathlib's, over the
`RingCat`-valued stalk of `𝒪_X ⋙ forget₂ CommRingCat RingCat`. Everything here is phrased with
the first, which is the one `stalkPairing` is stated for; the second never appears, because the
hypotheses of `nonempty_over_iso_free_of_inj_of_surj` quantify over *sections* of the structure
sheaf and mention no stalk of it. The germ map of Tag 01CB and the one of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/StalkFreeCover.lean` are definitionally equal,
which is what lets `Stacks.SheafOfModules.TensorStalkRingedSpace.grpGerm` and
  `Stacks.SheafOfModules.germ` appear in the same
computation.

Everything is stated for `RingedSpace.{u, u}` and `SheafOfModules.{u}`, matching
Tag 01CB: the site `Opens X` forces the carrier, ring and module
universes to agree.

The trivializing free module is indexed by `PUnit`, so the rank-one conclusion comes from
`Stacks.SheafOfModules.Invertible.freeUniqueIso` rather than from an equivalence with `Fin 1`,
and `Invertible.IsLocallyTrivial` is the intermediate predicate rather than a
`LocalGeneratorsData` built by hand.

**No Stacks attribute is attached anywhere in this file.** Tag 0B8M has three clauses: a finite
locally free module of rank one is invertible, the converse holds when the stalks are local
rings, and the converse fails in general. Only the second is proved here, and the equivalence
that the second clause is usually stated as needs the first for its other direction, so an
attribute keyed on the tag would report all three as formalized.

The space universe is specialized to the universe of the sections, `RingedSpace.{u, u}`, which is
the generality at which Tag 01CB is stated in this library and hence the limit of what
`stalkPairing` supports. The statement of Tag 0B8M leaves the space universe free. For a
scheme the two universes coincide, so the restriction is invisible to the intended consumers.

## References

* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 0AFW](https://stacks.math.columbia.edu/tag/0AFW)
-/

@[expose] public section

open CategoryTheory TensorProduct Opposite TopologicalSpace AlgebraicGeometry
  Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace Stacks.SheafOfModules

/-! ### The algebra of a pairing over a local ring -/

section LocalAlgebra

variable {A : Type u} [CommRing A] {M P : Type u} [AddCommGroup M] [Module A M]
  [AddCommGroup P] [Module A P]

/-- **A pairing over a local ring is trivialized by a single pure tensor.** If
`Θ : M ⊗[A] P ≃ₗ[A] A` and `A` is local, then `Θ (m ⊗ n) = 1` for some `m : M` and `n : P`.

Write `Θ⁻¹ 1` as a finite sum of pure tensors; their images under `Θ` sum to `1`, so they cannot
all lie in the maximal ideal, and rescaling the second factor of a summand pairing to a unit
produces a summand pairing to `1`. -/
theorem exists_tmul_eq_one_of_isLocalRing [IsLocalRing A] (Θ : M ⊗[A] P ≃ₗ[A] A) :
    ∃ (m : M) (n : P), Θ (m ⊗ₜ n) = 1 := by
  classical
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset (Θ.symm 1)
  have hsum : ∑ p ∈ S, Θ (p.1 ⊗ₜ[A] p.2) = 1 := by
    rw [← map_sum, ← hS, Θ.apply_symm_apply]
  have hex : ∃ p ∈ S, IsUnit (Θ (p.1 ⊗ₜ[A] p.2)) := by
    by_contra h
    have hmem : (1 : A) ∈ IsLocalRing.maximalIdeal A := by
      rw [← hsum]
      refine Ideal.sum_mem _ fun p hp => ?_
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact fun hu => h ⟨p, hp, hu⟩
    exact (Ideal.ne_top_iff_one _).mp (IsLocalRing.maximalIdeal.isMaximal A).ne_top hmem
  obtain ⟨p, -, v, hv⟩ := hex
  refine ⟨p.1, ((v⁻¹ : Aˣ) : A) • p.2, ?_⟩
  rw [TensorProduct.tmul_smul, map_smul, ← hv, smul_eq_mul]
  exact v.inv_mul

/-- **A pure tensor pairing to `1` trivializes an invertible module.** If `M` is an invertible
`A`-module, `Θ : M ⊗[A] P ≃ₗ[A] A` and `Θ (m₀ ⊗ n₀) = 1`, then `a ↦ a • m₀` is a bijection
`A → M`.

Contraction against `n₀` is a left inverse of `a ↦ a • m₀`, and a left inverse of a linear map
into an invertible module is automatically a right inverse. -/
theorem bijective_smul_of_tmul_eq_one [Module.Invertible A M] (Θ : M ⊗[A] P ≃ₗ[A] A)
    (m₀ : M) (n₀ : P) (h : Θ (m₀ ⊗ₜ n₀) = 1) :
    Function.Bijective (fun a : A => a • m₀) := by
  set c : M →ₗ[A] A := Θ.toLinearMap ∘ₗ (TensorProduct.mk A M P).flip n₀ with hc
  set μ : A →ₗ[A] M := LinearMap.toSpanSingleton A M m₀ with hμ
  have hleft : Function.LeftInverse c μ := by
    intro a
    simp only [hc, hμ, LinearMap.coe_comp, Function.comp_apply, LinearMap.flip_apply,
      TensorProduct.mk_apply, LinearMap.toSpanSingleton_apply, LinearEquiv.coe_coe]
    rw [← TensorProduct.smul_tmul', map_smul, h, smul_eq_mul, mul_one]
  have hright : Function.RightInverse c μ := Module.Invertible.rightInverse_of_leftInverse hleft
  exact ⟨hleft.injective, fun m => ⟨c m, hright m⟩⟩

end LocalAlgebra

/-! ### Trivializing sections on a neighbourhood -/

section Trivialization

variable {X : RingedSpace.{u, u}} {L N : SheafOfModules.{u} (structureSheafRing X)}

/-- The germ of Tag 01CB and the germ of `StalkFreeCover` agree. -/
theorem grpGerm_eq_germ (M : SheafOfModules.{u} (structureSheafRing X)) (x : X.carrier)
    {U : Opens X.carrier} (hx : x ∈ U) (m : ToType (M.val.obj (op U))) :
    grpGerm X M.val x U hx m = germ M x hx m := rfl

/-- The germ of Tag 01CB of a restricted section is the germ of the original section. -/
private theorem grpGerm_res (M : SheafOfModules.{u} (structureSheafRing X)) {U V : Opens X.carrier}
    (f : V ⟶ U) {x : X.carrier} (hx : x ∈ V) (m : ToType (M.val.obj (op U))) :
    grpGerm X M.val x V hx (res M f m) = grpGerm X M.val x U (f.le hx) m :=
  germ_res (M := M) x f hx m

/-- The stalk of `L` at `x` is an invertible `𝒪_{X, x}`-module: the pairing with the stalk of
`N` identifies its tensor product with `𝒪_{X, x}`. -/
theorem module_invertible_grpGerm
    (ψ : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (L)).obj
      (N)) ≅ SheafOfModules.unit (structureSheafRing X)) (x : X.carrier) :
    Module.Invertible (ringStalk X x) (grpStalk X L.val x) :=
  .left (stalkPairing ψ x)

/-- **Sections trivializing the pairing near a point.** If the stalk of `𝒪_X` at `x` is a local
ring, a trivialization `ψ : L ⊗ N ≅ 𝒪_X` admits sections `s` of `L` and `b` of `N` on a
neighbourhood of `x` whose pairing is the unit section.

The suffix distinguishes this from `Stacks.SheafOfModules.exists_tensorPairing_eq_one` of
[Stacks, Tag 01CY], which starts from a given global section `s` of `L` and produces the matching
`b` over the whole nonvanishing open of `s`; here the open is produced along with both
sections. -/
theorem exists_tensorPairing_eq_one_nhds
    (ψ : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (L)).obj
      (N)) ≅ SheafOfModules.unit (structureSheafRing X))
    (x : X.carrier) [IsLocalRing (ringStalk X x)] :
    ∃ (U : Opens X.carrier) (_ : x ∈ U) (s : ToType (L.val.obj (op U)))
      (b : ToType (N.val.obj (op U))), tensorPairing ψ U s b = unitSection X U := by
  obtain ⟨m₀, n₀, hmn⟩ := exists_tmul_eq_one_of_isLocalRing (stalkPairing ψ x)
  obtain ⟨U₁, hxU₁, s₁, hs₁⟩ := exists_grpGerm_eq X L.val x m₀
  obtain ⟨U₂, hxU₂, b₂, hb₂⟩ := exists_grpGerm_eq X N.val x n₀
  have hxU₃ : x ∈ U₁ ⊓ U₂ := ⟨hxU₁, hxU₂⟩
  set s₃ := res L (homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁)) s₁ with hs₃
  set b₃ := res N (homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂)) b₂ with hb₃
  have hgs : grpGerm X L.val x (U₁ ⊓ U₂) hxU₃ s₃ = m₀ := (grpGerm_res L _ hxU₃ s₁).trans hs₁
  have hgb : grpGerm X N.val x (U₁ ⊓ U₂) hxU₃ b₃ = n₀ := (grpGerm_res N _ hxU₃ b₂).trans hb₂
  have hgerm : ringGerm X x (U₁ ⊓ U₂) hxU₃ (tensorPairing ψ (U₁ ⊓ U₂) s₃ b₃)
      = ringGerm X x (U₁ ⊓ U₂) hxU₃ (unitSection X (U₁ ⊓ U₂)) := by
    rw [← stalkPairing_germ ψ x (U₁ ⊓ U₂) hxU₃, hgs, hgb, hmn]
    exact (map_one (ringGerm X x (U₁ ⊓ U₂) hxU₃)).symm
  obtain ⟨W, hxW, j₁, j₂, hW⟩ := TopCat.Presheaf.germ_eq X.presheaf x hxU₃ hxU₃ _ _ hgerm
  refine ⟨W, hxW, res L j₁ s₃, res N j₁ b₃, ?_⟩
  refine (tensorPairing_res ψ j₁ s₃ b₃).symm.trans ?_
  refine Eq.trans ?_ (map_one (X.presheaf.map j₁.op).hom)
  rw [Subsingleton.elim j₂ j₁] at hW
  exact hW

/-- **At every point of the trivializing neighbourhood, multiplication by the germ of `s` is a
bijection onto the stalk of `L`.** The pairing identity `ψ (s ⊗ b) = 1` is read on germs at the
point, where `bijective_smul_of_tmul_eq_one` applies. -/
theorem bijective_smul_grpGerm_of_tensorPairing_eq_one
    {ψ : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (L)).obj
      (N)) ≅ SheafOfModules.unit (structureSheafRing X)}
    {U : Opens X.carrier} {s : ToType (L.val.obj (op U))} {b : ToType (N.val.obj (op U))}
    (hsb : tensorPairing ψ U s b = unitSection X U) (y : X.carrier) (hyU : y ∈ U)
    [IsLocalRing (ringStalk X y)] :
    Function.Bijective (fun a : ringStalk X y => a • grpGerm X L.val y U hyU s) := by
  have := module_invertible_grpGerm ψ y
  refine bijective_smul_of_tmul_eq_one (stalkPairing ψ y) _ (grpGerm X N.val y U hyU b) ?_
  rw [stalkPairing_germ ψ y U hyU, hsb]
  exact map_one (ringGerm X y U hyU)

/-- Multiplication of a section of `𝒪_X` over `V ≤ U` by the restriction of `s`, read on the
germ at a point of `V`. -/
theorem grpGerm_smul_res
    {U V : Opens X.carrier} (f : V ⟶ U) (s : ToType (L.val.obj (op U))) (y : X.carrier)
    (hyV : y ∈ V) (d : ToType ((structureSheafRing X).obj.obj (op V))) :
    ringGerm X y V hyV d • grpGerm X L.val y U (f.le hyV) s
      = grpGerm X L.val y V hyV (d • res L f s) := by
  rw [stalkModule_germ_smul X L.val y V hyV d (res L f s), grpGerm_res L f hyV s]

/-- **The trivializing section trivializes `L` on the whole neighbourhood.** Injectivity of
`c ↦ c • s` on the sections over each `V ≤ U` holds because a section of the structure sheaf
whose germs all vanish vanishes; local surjectivity holds because every germ of `L` at a point
of `V` is a multiple of the germ of `s`. -/
theorem nonempty_over_iso_unit_of_tensorPairing_eq_one
    {ψ : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (L)).obj
      (N)) ≅ SheafOfModules.unit (structureSheafRing X)}
    {U : Opens X.carrier} {s : ToType (L.val.obj (op U))} {b : ToType (N.val.obj (op U))}
    (hsb : tensorPairing ψ U s b = unitSection X U)
    [∀ y : X.carrier, IsLocalRing (ringStalk X y)] :
    Nonempty (L.over U ≅ SheafOfModules.unit ((structureSheafRing X).over U)) := by
  classical
  have key : ∀ (y : X.carrier) (hyU : y ∈ U), Function.Bijective
      (fun a : ringStalk X y => a • grpGerm X L.val y U hyU s) :=
    fun y hyU => bijective_smul_grpGerm_of_tensorPairing_eq_one hsb y hyU
  have hsingle : ∀ {V : Opens X.carrier} (f : V ⟶ U)
      (c : PUnit.{u + 1} → ToType ((structureSheafRing X).obj.obj (op V))),
      ∑ i : PUnit.{u + 1}, c i • res L f s = c PUnit.unit • res L f s := by
    intro V f c
    simp
  have hinj : ∀ ⦃V : Opens X.carrier⦄ (f : V ⟶ U), Function.Injective
      (fun c : PUnit.{u + 1} → ToType ((structureSheafRing X).obj.obj (op V)) =>
        ∑ i : PUnit.{u + 1}, c i • res L f s) := by
    intro V f c c' hcc
    have hcc' : c PUnit.unit • res L f s = c' PUnit.unit • res L f s := by
      rw [← hsingle f c, ← hsingle f c']
      exact hcc
    have hsec : ∀ d d' : ToType (X.presheaf.obj (op V)),
        (∀ (y : X.carrier) (hy : y ∈ V), ringGerm X y V hy d = ringGerm X y V hy d') → d = d' :=
      fun d d' hd => TopCat.Presheaf.section_ext X.sheaf V d d' fun y hy => hd y hy
    have hpt : c PUnit.unit = c' PUnit.unit := by
      refine hsec _ _ fun y hyV => (key y (f.le hyV)).injective ?_
      show ringGerm X y V hyV (c PUnit.unit) • grpGerm X L.val y U (f.le hyV) s
        = ringGerm X y V hyV (c' PUnit.unit) • grpGerm X L.val y U (f.le hyV) s
      rw [grpGerm_smul_res f s y hyV, grpGerm_smul_res f s y hyV]
      exact congrArg (grpGerm X L.val y V hyV) hcc'
    funext i
    obtain rfl : i = PUnit.unit := rfl
    exact hpt
  have hsurj : ∀ ⦃V : Opens X.carrier⦄ (f : V ⟶ U)
      (t : ToType (L.val.obj (op V))) (y : X.carrier), y ∈ V →
      ∃ (W : Opens X.carrier) (h : W ⟶ V), y ∈ W ∧
        ∃ c : PUnit.{u + 1} → ToType ((structureSheafRing X).obj.obj (op W)),
          res L h t = ∑ i : PUnit.{u + 1}, c i • res L (h ≫ f) s := by
    intro V f t y hyV
    obtain ⟨a, ha⟩ := (key y (f.le hyV)).surjective (grpGerm X L.val y V hyV t)
    have ha' : a • grpGerm X L.val y U (f.le hyV) s = grpGerm X L.val y V hyV t := ha
    obtain ⟨W₁, hyW₁, c₁, hc₁⟩ := X.presheaf.exists_germ_eq a
    have hyW : y ∈ V ⊓ W₁ := ⟨hyV, hyW₁⟩
    set g : V ⊓ W₁ ⟶ V := homOfLE inf_le_left with hg
    set k : V ⊓ W₁ ⟶ W₁ := homOfLE inf_le_right with hk
    set c : ToType ((structureSheafRing X).obj.obj (op (V ⊓ W₁))) := resR _ k c₁ with hcdef
    have hcg : ringGerm X y (V ⊓ W₁) hyW c = a := by
      rw [hcdef, hc₁.symm]
      exact TopCat.Presheaf.germ_res_apply X.presheaf k y hyW c₁
    have hge : grpGerm X L.val y (V ⊓ W₁) hyW (res L g t)
        = grpGerm X L.val y (V ⊓ W₁) hyW (c • res L (g ≫ f) s) := by
      rw [← grpGerm_smul_res (g ≫ f) s y hyW c, hcg, ha']
      exact grpGerm_res L g hyW t
    obtain ⟨W₂, h₂, hyW₂, hres⟩ :=
      exists_res_eq (M := L) y hyW (res L g t) (c • res L (g ≫ f) s) hge
    refine ⟨W₂, h₂ ≫ g, hyW₂, fun _ => resR _ h₂ c, ?_⟩
    have hassoc : (h₂ ≫ g) ≫ f = h₂ ≫ g ≫ f := Subsingleton.elim _ _
    have hgoal : res L h₂ (c • res L (g ≫ f) s)
        = resR (structureSheafRing X) h₂ c • res L ((h₂ ≫ g) ≫ f) s := by
      rw [res_smul, res_res, hassoc]
    rw [hsingle ((h₂ ≫ g) ≫ f) (fun _ => resR (structureSheafRing X) h₂ c), ← hgoal, ← hres]
    exact (res_res L g h₂ t).symm
  obtain ⟨e⟩ := nonempty_over_iso_free_of_inj_of_surj (ι := PUnit.{u + 1}) L (fun _ => s)
    (by intro V f; simpa using hinj f)
    (by
      intro V f t y hyV
      obtain ⟨W, h, hyW, c, hc⟩ := hsurj f t y hyV
      exact ⟨W, h, hyW, c, by simpa using hc⟩)
  exact ⟨e ≪≫ Invertible.freeUniqueIso PUnit.{u + 1}⟩

end Trivialization

/-! ### The converse clause of Tag 0B8M -/

section Main

namespace Invertible

variable {X : RingedSpace.{u, u}} (L : SheafOfModules.{u} (structureSheafRing X))
  [∀ y : X.carrier, IsLocalRing (ringStalk X y)]

/-- An invertible sheaf of modules on a ringed space all of whose stalks are local rings is
locally trivial: the trivializing neighbourhoods of `exists_tensorPairing_eq_one_nhds` cover the
space. -/
theorem isLocallyTrivial_of_isInvertible
    [IsInvertible X.presheaf (structureSheafRing X).property L] :
    Invertible.IsLocallyTrivial L := by
  classical
  obtain ⟨N, ⟨ψ⟩⟩ := (isInvertible_iff_exists_tensor_iso_unit
    (O := X.presheaf) (hO := (structureSheafRing X).property) L).mp ‹_›
  have key : ∀ x : X.carrier, ∃ U : Opens X.carrier, x ∈ U ∧
      Nonempty (L.over U ≅ SheafOfModules.unit ((structureSheafRing X).over U)) := by
    intro x
    obtain ⟨U, hxU, s, b, hsb⟩ := exists_tensorPairing_eq_one_nhds ψ x
    exact ⟨U, hxU, nonempty_over_iso_unit_of_tensorPairing_eq_one hsb⟩
  refine ⟨X.carrier, fun x => (key x).choose, ?_, fun x => (key x).choose_spec.2⟩
  rw [Opens.coversTop_iff]
  refine TopologicalSpace.IsOpenCover.mk (eq_top_iff.mpr ?_)
  intro x _
  exact Opens.mem_iSup.mpr ⟨x, (key x).choose_spec.1⟩

/-- **The converse clause of Stacks Tag 0B8M.** On a ringed space all of whose stalks
`𝒪_{X, x}` are local rings, an invertible sheaf of `𝒪_X`-modules is finite locally free of rank
one.

Both this and `Invertible.isLocallyTrivial_of_isInvertible` live in the `Invertible` namespace,
where the predicates they conclude live: `Invertible.IsLocallyTrivial` and
`Invertible.IsFiniteLocallyFreeOfRank`. The same conclusion for the *other* rank predicate of
[Stacks, Tag 01CS], `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank`, is
`Stacks.SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible` of
`StacksFrontier.AlgebraicGeometry.InvertibleTrivialization.Sheaf`, which deduces it from this one.
Local triviality has only this one proof: that file imports it from here.

No Stacks attribute is attached: Tag 0B8M has three clauses — the unconditional implication, this
converse, and the counterexample showing the local-ring hypothesis cannot be dropped — and only
this one is proved in the library, so an attribute here would report the whole tag as
formalized. -/
theorem isFiniteLocallyFreeOfRank_one_of_isInvertible
    [IsInvertible X.presheaf (structureSheafRing X).property L] :
    Invertible.IsFiniteLocallyFreeOfRank (R := structureSheafRing X) L 1 :=
  have := isLocallyTrivial_of_isInvertible L
  Invertible.isFiniteLocallyFreeOfRank_one_of_isLocallyTrivial L

/-- The converse clause of Tag 0B8M for the `AlgebraicGeometry` spelling of invertibility, which
agrees with the `Stacks` one by `isInvertible_iff_algebraicGeometry`. -/
theorem isFiniteLocallyFreeOfRank_one_of_isInvertible_algebraicGeometry
    [h : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X).property L] :
    Invertible.IsFiniteLocallyFreeOfRank (R := structureSheafRing X) L 1 :=
  have := IsInvertible.ofAlgebraicGeometry X.presheaf (structureSheafRing X).property L h
  isFiniteLocallyFreeOfRank_one_of_isInvertible L

end Invertible

end Main

end Stacks.SheafOfModules

end
