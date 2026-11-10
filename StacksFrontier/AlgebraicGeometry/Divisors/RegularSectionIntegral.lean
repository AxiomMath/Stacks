module

public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeRegular
public import StacksFrontier.AlgebraicGeometry.TorsionQuasicoherent.Basic

/-!
# A nonzero section of an invertible module on an integral scheme is regular

Let `X` be an integral scheme and `L` an invertible `𝒪_X`-module. This file proves that a
global section of `L` that is nonzero is a nonzerodivisor, that is, that multiplication by it
is a monomorphism `𝒪_X ⟶ L` in the sense of [Stacks, Tag 01WY].

## Main results

* `AlgebraicGeometry.eq_zero_of_map_le_top_eq_zero_of_isIntegral`: a global section of `L` whose
  restriction to one nonempty open vanishes is zero.
* `AlgebraicGeometry.eq_of_smul_map_le_top_eq_of_isIntegral`: multiplication by a nonzero global
  section of `L` is injective on the sections of the structure sheaf over every open.
* `AlgebraicGeometry.isRegularSection_of_eval_top_ne_zero`: a nonzero global section of `L` is a
  nonzerodivisor.
* `AlgebraicGeometry.isEffectiveCartierDivisor_zeroScheme_of_ne_zero`: the zero scheme of a
  nonzero global section of `L` is an effective Cartier divisor.
* `AlgebraicGeometry.injective_stalkFunctor_map_unitHomEquiv_symm_of_eval_top_ne_zero`:
  multiplication by a nonzero global section of `L` is injective on every stalk.

## Implementation notes

The three statements are proved in that order, and the second two are the nonzerodivisor
argument of `AlgebraicGeometry.isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection` with
the source of the cancellation changed. There, on a trivializing affine open `U` with
`e : Γ(L, U) ≃ₗ Γ(X, U)`, the coordinate `a = e (s|_U)` has nonzerodivisor germs because the
zero scheme of `s` is an effective Cartier divisor. Here `Γ(X, U)` is a domain, by
`AlgebraicGeometry.IsIntegral.component_integral` and the nonemptiness of `U`, and `a ≠ 0`, so
the cancellation is `mul_right_cancel₀`. Nothing about divisors is used.

So the mathematical content is confined to the first statement, and it is the one place where
the module has to be invertible rather than merely quasi-coherent: the restriction maps of a
quasi-coherent module on an integral scheme are not injective in general — a torsion module is
the counterexample — and invertibility rules torsion out one trivializing open at a time. The
generic point `η` lies in every nonempty open, so after intersecting a trivializing affine open
`V` with the given nonempty open the germ of `s` at `η` vanishes on `V`; then
`Stacks.AlgebraicGeometry.TorsionQuasicoherent.exists_ne_zero_smul_eq_zero`, which is the half
of [Stacks, Tag 0AXR] stating that such a section is annihilated by a nonzero function, gives
`b • s|_V = 0` with `b ≠ 0`, and `e` turns that into `b * a = 0` in the domain `Γ(X, V)`. Hence
`s` dies on every trivializing affine open, and the opens of that kind cover `X`.

Components of a global section are spelled as restrictions from `⊤`, never as `s.eval (.op U)`
retyped at `Γ(L, U)`, for the reason `ZeroSchemeRegular.lean` gives: the retyping is erased by
`simp`, which then loses the `Γ(X, U)`-module structure on `Γ(L, U)`.

`AlgebraicGeometry.isEffectiveCartierDivisor_zeroScheme_of_ne_zero` is the same statement read
through [Stacks, Tag 02OR] (4), and is stated for a global section in the form `Γ(L, ⊤)` rather
than for an element of `L.sections`, because that is the form a section produced by a
construction has; the compatible family of its restrictions is built inside the proof.

## References

* [Stacks Project, Tag 01WY](https://stacks.math.columbia.edu/tag/01WY)
* [Stacks Project, Tag 0AXR](https://stacks.math.columbia.edu/tag/0AXR)
* [Stacks Project, Tag 0B40](https://stacks.math.columbia.edu/tag/0B40)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.TorsionQuasicoherent

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}} [IsIntegral X] (L : X.Modules)
  [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]

include L in
/-- On a trivializing affine open of an integral scheme, a section of an invertible module whose
germ at the generic point vanishes is zero: it is annihilated by a nonzero function, and its
coordinate under the trivialization lives in a domain. -/
private theorem eq_zero_of_germ_genericPoint_eq_zero (U : X.affineOpens) [Nonempty U.1]
    (e : Γ(L, U.1) ≃ₗ[Γ(X, U.1)] Γ(X, U.1)) {s : Γ(L, U.1)}
    (hs : L.presheaf.germ U.1 (genericPoint X) (genericPoint_mem U.1) s = 0) :
    s = 0 := by
  have := isQuasicoherent_of_isInvertible L
  obtain ⟨b, hb, hbs⟩ := exists_ne_zero_smul_eq_zero L U.2 hs
  have : IsDomain Γ(X, U.1) := IsIntegral.component_integral U.1
  have hba : b * e s = 0 := by rw [← smul_eq_mul, ← map_smul, hbs, map_zero]
  have hes : e s = 0 := (mul_eq_zero.mp hba).resolve_left hb
  simpa using e.injective (by simpa using hes)

include L in
/-- **A global section of an invertible module on an integral scheme that dies on one nonempty
open is zero.** The generic point lies in that open and in every trivializing affine open, so
the section has vanishing germ at the generic point of each trivializing affine open and
therefore vanishes on it; those opens cover the space. -/
theorem eq_zero_of_map_le_top_eq_zero_of_isIntegral (s : Γ(L, ⊤)) {U : X.Opens} [Nonempty U]
    (hU : L.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s = 0) : s = 0 := by
  have hUne : (U : Set X).Nonempty := Set.nonempty_coe_sort.mp ‹Nonempty U›
  apply TopCat.Presheaf.section_ext
    (⟨L.val.presheaf, L.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat.{u} X.toTopCat)
    ⊤ s 0
  intro x hx
  obtain ⟨V, hxV, -, ⟨e⟩⟩ := exists_affineOpens_linearEquiv_le X L x ⊤ hx
  have hVn : Nonempty (V.1 : X.Opens) := ⟨⟨x, hxV⟩⟩
  have hVne : (V.1 : Set X).Nonempty := ⟨x, hxV⟩
  obtain ⟨y, hy⟩ := nonempty_preirreducible_inter V.1.isOpen U.isOpen hVne hUne
  have hWn : Nonempty (V.1 ⊓ U : X.Opens) := ⟨⟨y, hy⟩⟩
  have hWV : (V.1 ⊓ U : X.Opens) ≤ V.1 := inf_le_left
  have hWU : (V.1 ⊓ U : X.Opens) ≤ U := inf_le_right
  have hW : L.presheaf.map (homOfLE (le_top : (V.1 ⊓ U : X.Opens) ≤ ⊤)).op s = 0 := by
    rw [← Scheme.Modules.map_map_le_top L s hWU, hU, map_zero]
  have hgerm : L.presheaf.germ V.1 (genericPoint X) (genericPoint_mem V.1)
      (L.presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op s) = 0 := by
    rw [← L.presheaf.germ_res_apply (homOfLE hWV) (genericPoint X)
      (genericPoint_mem (V.1 ⊓ U : X.Opens)), Scheme.Modules.map_map_le_top L s hWV, hW,
      map_zero]
  rw [map_zero]
  change (L.presheaf.germ ⊤ x hx) s = 0
  rw [← L.presheaf.germ_res_apply (homOfLE (show V.1 ≤ ⊤ from le_top)) x hxV,
    eq_zero_of_germ_genericPoint_eq_zero L V e hgerm, map_zero]

include L in
/-- **Cancelling a nonzero global section of an invertible module on an integral scheme.**
Multiplication by such a section is injective on the sections of the structure sheaf over every
open: on a trivializing affine open the identity becomes one in the domain `Γ(X, U)` with a
nonzero factor to cancel. -/
theorem eq_of_smul_map_le_top_eq_of_isIntegral (s : Γ(L, ⊤)) (hs : s ≠ 0)
    (T : X.Opens) {r t : Γ(X, T)}
    (hrt : r • L.presheaf.map (homOfLE (le_top : T ≤ ⊤)).op s =
      t • L.presheaf.map (homOfLE (le_top : T ≤ ⊤)).op s) : r = t := by
  apply TopCat.Presheaf.section_ext
    (⟨X.presheaf, X.IsSheaf⟩ : TopCat.Sheaf CommRingCat.{u} X.toTopCat) T r t
  intro x hx
  obtain ⟨U, hxU, hUT, ⟨e⟩⟩ := exists_affineOpens_linearEquiv_le X L x T hx
  have hUn : Nonempty (U.1 : X.Opens) := ⟨⟨x, hxU⟩⟩
  set a : Γ(X, U.1) := e (L.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op s) with hadef
  have ha : a ≠ 0 := by
    intro h0
    refine hs (eq_zero_of_map_le_top_eq_zero_of_isIntegral L s (U := U.1) (e.injective ?_))
    rw [map_zero, ← hadef, h0]
  have hres := congrArg (fun z : Γ(L, T) => L.presheaf.map (homOfLE hUT).op z) hrt
  simp only [Scheme.Modules.map_smul, Scheme.Modules.map_map_le_top L s hUT] at hres
  have hcoord (q : Γ(X, U.1)) :
      e (q • L.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op s) = q * a := by
    rw [map_smul, hadef, smul_eq_mul]
  have hprod : (X.presheaf.map (homOfLE hUT).op).hom r * a =
      (X.presheaf.map (homOfLE hUT).op).hom t * a := by
    simpa only [hcoord] using congrArg e hres
  have : IsDomain Γ(X, U.1) := IsIntegral.component_integral U.1
  rw [← congrArg (fun φ => φ r) (X.presheaf.germ_res (homOfLE hUT) x hxU),
    ← congrArg (fun φ => φ t) (X.presheaf.germ_res (homOfLE hUT) x hxU)]
  exact congrArg (X.presheaf.germ U.1 x hxU).hom (mul_right_cancel₀ ha hprod)

include L in
/-- **A nonzero global section of an invertible module on an integral scheme is a
nonzerodivisor**, in the sense of [Stacks, Tag 01WY]: multiplication by it is a monomorphism
`𝒪_X ⟶ L`. -/
theorem isRegularSection_of_eval_top_ne_zero (s : L.sections) (hs : s.eval (op ⊤) ≠ 0) :
    IsRegularSection X.sheaf.obj X.ringCatSheaf.property s := by
  have hreflect : Functor.ReflectsMonomorphisms (SheafOfModules.forget X.ringCatSheaf) :=
    Functor.reflectsMonomorphisms_of_faithful _
  refine hreflect.reflects (L.unitHomEquiv.symm s) ?_
  refine PresheafOfModules.mono_of_injective fun T r t hrt => ?_
  refine eq_of_smul_map_le_top_eq_of_isIntegral L (s.eval (op ⊤)) hs T.unop ?_
  rwa [← Scheme.Modules.unitHomEquiv_symm_app_apply L s T.unop r,
    ← Scheme.Modules.unitHomEquiv_symm_app_apply L s T.unop t]

include L in
/-- **The zero scheme of a nonzero global section of an invertible module on an integral scheme
is an effective Cartier divisor.** The section is a nonzerodivisor, and the zero scheme of a
nonzerodivisor section is an effective Cartier divisor by [Stacks, Tag 02OR] (4). -/
theorem isEffectiveCartierDivisor_zeroScheme_of_ne_zero (s : Γ(L, ⊤)) (hs : s ≠ 0) :
    Stacks.Divisors.IsEffectiveCartierDivisor (zeroScheme X L s) := by
  let t : L.sections := L.val.sectionsMk
    (fun U => L.val.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op s) (by
      intro U V f
      change L.presheaf.map f (L.presheaf.map (homOfLE le_top).op s) =
        L.presheaf.map (homOfLE le_top).op s
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl)
  have heval : t.eval (op ⊤) = s := by
    change L.presheaf.map (𝟙 (op ⊤)) s = s
    simp
  exact heval ▸ (isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection X L t).mpr
    (isRegularSection_of_eval_top_ne_zero L t (by rwa [heval]))

include L in
/-- **Multiplication by a nonzero global section of an invertible module on an integral scheme is
injective on every stalk.** Injectivity on the sections over every open is
`AlgebraicGeometry.Scheme.Modules.injective_unitHomEquiv_symm_app_of_isRegularSection` applied to
`AlgebraicGeometry.isRegularSection_of_eval_top_ne_zero`, and a map of presheaves injective on
every open is injective on every stalk, because a stalk is a filtered colimit of the sections:
`TopCat.Presheaf.stalkFunctor_map_injective_of_app_injective`. -/
theorem injective_stalkFunctor_map_unitHomEquiv_symm_of_eval_top_ne_zero (s : L.sections)
    (hs : s.eval (op ⊤) ≠ 0) (x : X) :
    Function.Injective (ConcreteCategory.hom
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((Scheme.Modules.toPresheaf X).map (L.unitHomEquiv.symm s)))) :=
  TopCat.Presheaf.stalkFunctor_map_injective_of_app_injective
    (fun U => Scheme.Modules.injective_unitHomEquiv_symm_app_of_isRegularSection L s
      (isRegularSection_of_eval_top_ne_zero L s hs) U) x

end AlgebraicGeometry

end
