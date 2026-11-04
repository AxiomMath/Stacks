module

public import Mathlib.Topology.Sheaves.LocallySurjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardRightExact
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeFactorization
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeRegular
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeSequence

/-!
# The exact sequence of a regular section

Let `L` be an invertible module on a scheme `X`, let `s` be a global section of `L`, write
`f : 𝒪_X ⟶ L` for multiplication by `s` and let `i : Z(s) ⟶ X` be the inclusion of the zero
scheme of `s` ([Stacks, Tag 02OQ]). [Stacks, Tag 0C6K](https://stacks.math.columbia.edu/tag/0C6K)
asserts two things:

1. the unit `g : L ⟶ i_* i^* L` of the pullback–pushforward adjunction realizes `i_* i^* L` as
   the cokernel of `f`, i.e. there is an isomorphism `e : coker f ≅ i_* i^* L` with
   `coker.π f ≫ e.hom = g`;
2. if `s` is a nonzerodivisor ([Stacks, Tag 01WY]) then
   `0 ⟶ 𝒪_X ⟶ L ⟶ i_* i^* L ⟶ 0` is short exact.

Both are proved here.

## Main results

* `AlgebraicGeometry.exists_cokernelIso_unit_zeroScheme`: the unit `g` realizes `i_* i^* L` as the
  cokernel of `f`.
* `AlgebraicGeometry.shortExact_zeroScheme_of_isRegularSection`: for a regular section,
  `0 ⟶ 𝒪_X ⟶ L ⟶ i_* i^* L ⟶ 0` is short exact.
* `AlgebraicGeometry.section_comp_unit_zeroScheme_eq_zero`: the composite `𝒪_X ⟶ L ⟶ i_* i^* L`
  vanishes.
* `AlgebraicGeometry.smul_eq_zero_of_mem_ker_subschemeι`: the defining ideal of the zero scheme
  annihilates any quotient of `L` that kills `s`.

## Implementation notes

Sections of `𝒪_X`-modules are written in the `Γ` API of
`Mathlib/AlgebraicGeometry/Modules/Sheaf.lean` (`Γ(M, U)`,
`AlgebraicGeometry.Scheme.Modules.Hom.app`, `AlgebraicGeometry.Scheme.Modules.map_smul`)
throughout, which is the spelling the zero-scheme API already uses and the one the
`Module Γ(X, U) Γ(M, U)` instance is found at. The `ModuleCat` spelling `M.val.obj (op U)` works
too, but mixing them does not: `Γ(X, U)` scalars acting on a `ModuleCat`-spelled section fails
instance search.

The one declaration that needs
`attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules …` is
`AlgebraicGeometry.isLocallySurjective_mapPresheaf_of_epi`, because `Epi` in `X.Modules` and `Epi`
in `SheafOfModules X.ringCatSheaf` are different statements about the same morphism — the
`Category X.Modules` instance has its own `Hom` field — and
`Stacks.SheafOfModules.EpiMono.isLocallySurjective_of_epi` is stated for the latter. The attribute
is confined to that declaration with `in`, because file-wide it makes `p.app` resolve through
`SheafOfModules.Hom` and the `Γ`-level field notation stops working.

## References

* [Stacks Project, Tag 0C6K](https://stacks.math.columbia.edu/tag/0C6K)
* [Stacks Project, Tag 02OQ](https://stacks.math.columbia.edu/tag/02OQ)
* [Stacks Project, Tag 01WY](https://stacks.math.columbia.edu/tag/01WY)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- If `a` is a multiple of the coordinate of `s` in a trivialization `e`, then `a • m` is a
multiple of `s` for every `m`. -/
private theorem smul_eq_of_coordinate {R N : Type*} [CommRing R] [AddCommGroup N] [Module R N]
    (e : N ≃ₗ[R] R) (s m : N) (a : R) (ha : a ∈ Ideal.span ({e s} : Set R)) :
    ∃ b : R, a • m = b • s := by
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp ha
  refine ⟨b * e m, e.injective ?_⟩
  simp only [map_smul, smul_eq_mul]
  rw [hb]
  ring

variable (X : Scheme.{u}) (L : X.Modules)

attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules
  AlgebraicGeometry.Scheme.Modules.Hom AlgebraicGeometry.Scheme.Modules.instCategory in
/-- An epimorphism of `𝒪_X`-modules is locally surjective on sections. -/
theorem isLocallySurjective_mapPresheaf_of_epi {A B : X.Modules} (p : A ⟶ B) [Epi p] :
    TopCat.Presheaf.IsLocallySurjective (Scheme.Modules.Hom.mapPresheaf p) :=
  Stacks.SheafOfModules.EpiMono.isLocallySurjective_of_epi p

variable [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]

/-- **The pullback of a global section to its own zero scheme vanishes.** -/
theorem pullbackGlobalSections_subschemeι_zeroScheme_eq_zero (s : Γ(L, ⊤)) :
    pullbackGlobalSections (zeroScheme X L s).subschemeι L s = 0 :=
  (pullbackSection_eq_zero_iff_factorsThrough_zeroScheme X L s
    (zeroScheme X L s).subschemeι).2 ⟨𝟙 _, by simp⟩

/-- The image of the global section `s` under the unit `L ⟶ i_* i^* L` vanishes over every open,
for `i` the inclusion of the zero scheme of `s`. -/
theorem sectionsMap_unit_zeroScheme_eq_zero (s : L.sections) :
    let i := (zeroScheme X L (s.eval (op ⊤))).subschemeι
    let g : L ⟶ (Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj L) :=
      (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app L
    ∀ U, (SheafOfModules.sectionsMap g s).eval U = 0 := by
  dsimp only
  intro U
  set i := (zeroScheme X L (s.eval (op ⊤))).subschemeι
  let g : L ⟶ (Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj L) :=
    (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app L
  let M : X.Modules := (Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj L)
  have he : i ⁻¹ᵁ (⊤ : X.Opens) = ⊤ := by ext x; simp
  let p := ((Scheme.Modules.pullback i).obj L).presheaf.map (eqToHom he).op
  have hpIso : IsIso p := inferInstanceAs (IsIso
    (((Scheme.Modules.pullback i).obj L).presheaf.mapIso (eqToIso he).op).hom)
  have hp : ConcreteCategory.hom p ((SheafOfModules.sectionsMap g s).eval (op ⊤)) = 0 := by
    show pullbackGlobalSections i L (s.eval (op ⊤)) = 0
    exact pullbackGlobalSections_subschemeι_zeroScheme_eq_zero X L _
  have htop : (SheafOfModules.sectionsMap g s).eval (op ⊤) = 0 :=
    (ConcreteCategory.bijective_of_isIso p).1 (hp.trans (map_zero _).symm)
  have h := PresheafOfModules.sections_property (SheafOfModules.sectionsMap g s)
    (homOfLE (show U.unop ≤ ⊤ from le_top)).op
  have hmap : (ConcreteCategory.hom (M.val.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op))
      ((SheafOfModules.sectionsMap g s).eval (op ⊤)) = 0 := by
    rw [htop, map_zero]
  exact h.symm.trans hmap

/-- **Multiplication by `s` followed by restriction to its zero scheme is zero.** -/
theorem section_comp_unit_zeroScheme_eq_zero (s : L.sections) :
    let i := (zeroScheme X L (s.eval (op ⊤))).subschemeι
    let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
    let f : O ⟶ L := L.unitHomEquiv.symm s
    let g : L ⟶ (Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj L) :=
      (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app L
    f ≫ g = 0 := by
  intro i O f g
  refine (SheafOfModules.unitHomEquiv_symm_comp s g).trans ((Equiv.symm_apply_eq _).2 ?_)
  exact PresheafOfModules.sections_ext _ _ fun U =>
    (sectionsMap_unit_zeroScheme_eq_zero X L s U).trans rfl

/-- **The defining ideal of the zero scheme annihilates every quotient of `L` that kills `s`.** If
`p : L ⟶ M` is an epimorphism of `𝒪_X`-modules killing the section `s`, then every function on an
open `U` lying in the kernel of the comorphism of `Z(s) ⟶ X` annihilates every section of `M` over
`U`. -/
theorem smul_eq_zero_of_mem_ker_subschemeι (s : L.sections) (M : X.Modules) (p : L ⟶ M) [Epi p]
    (hp : ∀ W : X.Opens, Scheme.Modules.Hom.app p W
      (L.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (s.eval (op ⊤))) = 0)
    (U : X.Opens) (a : Γ(X, U))
    (ha : ((zeroScheme X L (s.eval (op ⊤))).subschemeι.app U).hom a = 0) (m : Γ(M, U)) :
    a • m = 0 := by
  classical
  refine TopCat.Presheaf.IsSheaf.section_ext (F := Scheme.Modules.presheaf M) M.isSheaf
    (U := op U) (s := a • m) (t := 0) ?_
  intro x hx
  obtain ⟨V₀, hV₀, ⟨l, hl⟩, hxV₀⟩ :=
    (TopCat.Presheaf.isLocallySurjective_iff (Scheme.Modules.Hom.mapPresheaf p)).mp
      (isLocallySurjective_mapPresheaf_of_epi X p) U m x hx
  obtain ⟨W, hxW, hWV₀, ⟨e⟩⟩ := exists_affineOpens_linearEquiv_le X L x V₀ hxV₀
  have hWU : W.1 ≤ U := hWV₀.trans hV₀
  refine ⟨W.1, hWU, hxW, ?_⟩
  have hπ : Scheme.Modules.Hom.app p W.1 (L.presheaf.map (homOfLE hWV₀).op l) =
      M.presheaf.map (homOfLE hWU).op m := by
    calc Scheme.Modules.Hom.app p W.1 (L.presheaf.map (homOfLE hWV₀).op l)
        = M.presheaf.map (homOfLE hWV₀).op (Scheme.Modules.Hom.app p V₀ l) :=
          CategoryTheory.congr_fun
            ((Scheme.Modules.Hom.mapPresheaf p).naturality (homOfLE hWV₀).op) l
      _ = M.presheaf.map (homOfLE hWV₀).op (M.presheaf.map (homOfLE hV₀).op m) :=
          congrArg (ConcreteCategory.hom (M.presheaf.map (homOfLE hWV₀).op)) hl
      _ = M.presheaf.map (homOfLE hWU).op m := by
          rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
          rfl
  set t := L.presheaf.map (homOfLE (le_top : W.1 ≤ ⊤)).op (s.eval (op ⊤))
  have ht0 : Scheme.Modules.Hom.app p W.1 t = 0 := hp W.1
  have hideal : (zeroScheme X L (s.eval (op ⊤))).ideal W =
      Ideal.span ({e t} : Set Γ(X, W.1)) :=
    zeroScheme_ideal_of_trivialization X L (s.eval (op ⊤)) W e _ rfl
  have haI : X.presheaf.map (homOfLE hWU).op a ∈
      Ideal.span ({e t} : Set Γ(X, W.1)) := by
    rw [← hideal, ← (zeroScheme X L (s.eval (op ⊤))).ker_subschemeι_app W]
    exact (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion
      (zeroScheme X L (s.eval (op ⊤))).subschemeι).map_mem_kernelIdeal (homOfLE hWU).op a ha
  obtain ⟨b, hb⟩ := smul_eq_of_coordinate e t
    (L.presheaf.map (homOfLE hWV₀).op l) (X.presheaf.map (homOfLE hWU).op a) haI
  calc M.presheaf.map (homOfLE hWU).op (a • m)
      = X.presheaf.map (homOfLE hWU).op a • M.presheaf.map (homOfLE hWU).op m :=
        M.map_smul _ _ _
    _ = X.presheaf.map (homOfLE hWU).op a •
          Scheme.Modules.Hom.app p W.1 (L.presheaf.map (homOfLE hWV₀).op l) := by rw [hπ]
    _ = Scheme.Modules.Hom.app p W.1
          (X.presheaf.map (homOfLE hWU).op a • L.presheaf.map (homOfLE hWV₀).op l) :=
        (Scheme.Modules.Hom.app_smul p _ _).symm
    _ = Scheme.Modules.Hom.app p W.1
          (b • t) := by rw [hb]
    _ = b • Scheme.Modules.Hom.app p W.1 t :=
        Scheme.Modules.Hom.app_smul p _ _
    _ = 0 := by rw [ht0, smul_zero]
    _ = M.presheaf.map (homOfLE hWU).op 0 := (map_zero _).symm

/-- In an adjunction `P ⊣ R`, if `P` kills `f` and the unit is an isomorphism at `coker f`, then
`R (P N)` *is* the cokernel of `f`, compatibly with the unit. -/
theorem exists_cokernelIso_of_isIso_unit_app {A B : Type*} [Category A] [Category B]
    [Limits.HasZeroMorphisms A] [Limits.HasZeroMorphisms B] {P : A ⥤ B} {R : B ⥤ A}
    (adj : P ⊣ R) [P.PreservesZeroMorphisms] [R.PreservesZeroMorphisms] {M N : A} (f : M ⟶ N)
    [Limits.HasCokernel f] [Limits.PreservesColimit (Limits.parallelPair f 0) P]
    [IsIso (adj.unit.app (Limits.cokernel f))] (hf : f ≫ adj.unit.app N = 0) :
    ∃ e : Limits.cokernel f ≅ R.obj (P.obj N),
      Limits.cokernel.π f ≫ e.hom = adj.unit.app N := by
  have hPf : P.map f = 0 := by
    apply (adj.homEquiv M (P.obj N)).injective
    show adj.unit.app M ≫ R.map (P.map f) = adj.unit.app M ≫ R.map 0
    show adj.unit.app M ≫ (P ⋙ R).map f = _
    rw [← adj.unit.naturality f]
    simpa using hf
  have hcol := Limits.isColimitOfHasCokernelOfPreservesColimit P f
  have : IsIso (P.map (Limits.cokernel.π f)) :=
    Limits.CokernelCofork.IsColimit.isIso_π _ hcol hPf
  refine ⟨asIso (adj.unit.app (Limits.cokernel f)) ≪≫
    (R.mapIso (asIso (P.map (Limits.cokernel.π f)))).symm, ?_⟩
  show Limits.cokernel.π f ≫ adj.unit.app (Limits.cokernel f) ≫ _ = _
  have hn := adj.unit.naturality (Limits.cokernel.π f)
  simp only [Functor.id_map, Functor.comp_map] at hn
  rw [← Category.assoc, hn]
  simp only [Category.assoc, Iso.symm_hom, Functor.mapIso_inv, asIso_inv, ← Functor.map_comp,
    IsIso.hom_inv_id]
  rw [R.map_id]
  exact Category.comp_id _

/-- For an invertible module `L` on a scheme `X` and a global section `s`, the unit of the
pullback–pushforward adjunction along the inclusion `i` of the zero scheme `Z(s)` realizes
`i_* i^* L` as the cokernel of multiplication by `s`.

No regularity hypothesis on `s` is needed. -/
@[stacks 0C6K "regular_section_sequence"]
theorem exists_cokernelIso_unit_zeroScheme (s : L.sections) :
    let i := (zeroScheme X L (s.eval (op ⊤))).subschemeι
    ∃ e : cokernel (L.unitHomEquiv.symm s) ≅
        (Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj L),
      cokernel.π (L.unitHomEquiv.symm s) ≫ e.hom =
        (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app L := by
  dsimp only
  set i := (zeroScheme X L (s.eval (op ⊤))).subschemeι
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let f : O ⟶ L := L.unitHomEquiv.symm s
  have hker : ∀ W : X.Opens, Scheme.Modules.Hom.app (cokernel.π f) W
      (L.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (s.eval (op ⊤))) = 0 := by
    intro W
    have hf1 : Scheme.Modules.Hom.app f W (1 : Γ(X, W)) =
        L.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (s.eval (op ⊤)) := by
      have h := Scheme.Modules.unitHomEquiv_symm_app_apply L s W (1 : Γ(X, W))
      rw [one_smul] at h
      exact h
    have h2 : Scheme.Modules.Hom.app (f ≫ cokernel.π f) W (1 : Γ(X, W)) = 0 := by
      rw [cokernel.condition f, Scheme.Modules.Hom.zero_app]
      rfl
    rw [← hf1]
    exact h2
  have hiso : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app (cokernel f)) :=
    Stacks.ClosedImmersion.isIso_unit_app_of_smul_eq_zero i (cokernel f)
      fun U a ha m => smul_eq_zero_of_mem_ker_subschemeι X L s (cokernel f) (cokernel.π f)
        hker U a ha m
  exact exists_cokernelIso_of_isIso_unit_app
    (Scheme.Modules.pullbackPushforwardAdjunction i) f
    (section_comp_unit_zeroScheme_eq_zero X L s)

/-- For an invertible module `L` on a scheme `X` and a regular global section `s`
([Stacks, Tag 01WY]), the sequence `0 ⟶ 𝒪_X ⟶ L ⟶ i_* i^* L ⟶ 0` is short exact, where `i` is the
inclusion of the zero scheme of `s`. -/
@[stacks 0C6K "regular_section_sequence"]
theorem shortExact_zeroScheme_of_isRegularSection (s : L.sections)
    (hs : IsRegularSection X.sheaf.obj X.ringCatSheaf.property s) :
    let i := (zeroScheme X L (s.eval (op ⊤))).subschemeι
    let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
    let f : O ⟶ L := L.unitHomEquiv.symm s
    let g : L ⟶ (Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj L) :=
      (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app L
    ∃ h : f ≫ g = 0, (ShortComplex.mk f g h).ShortExact :=
  Scheme.Modules.shortExact_of_isRegularSection_zeroScheme X L s hs
    (exists_cokernelIso_unit_zeroScheme X L s)

end AlgebraicGeometry

end
