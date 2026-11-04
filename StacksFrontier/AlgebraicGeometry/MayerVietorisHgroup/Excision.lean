module

public import StacksFrontier.AlgebraicGeometry.MayerVietorisHgroup.AmbientOpen

/-!
# Excision: a cover piece carrying no cohomology can be removed

Let `U`, `V` be two opens of a space covering a third open `W = U ⊔ V`, and let `F` be a sheaf of
modules whose cohomology over `V` and over `U ⊓ V` vanishes in *every* degree.  Then the
restriction map

`Hⁿ(W, F) ⟶ Hⁿ(U, F)`

is an isomorphism for every `n`.  This is the excision step: the piece `V` of the cover, being
acyclic for `F` together with its overlap, contributes nothing, so cohomology over the union is
cohomology over `U` alone.

The proof is the Mayer--Vietoris sequence of
`StacksFrontier/AlgebraicGeometry/MayerVietorisHgroup/AmbientOpen.lean` with its two outer terms
killed.  Writing the six-term window at degree `n` as

`Hⁿ(W) ⟶ Hⁿ(U) ⊞ Hⁿ(V) ⟶ Hⁿ(U ⊓ V) ⟶ Hⁿ⁺¹(W) ⟶ Hⁿ⁺¹(U) ⊞ Hⁿ⁺¹(V) ⟶ Hⁿ⁺¹(U ⊓ V)`,

exactness at the second position makes the first map epi as soon as `Hⁿ(U ⊓ V, F) = 0`, and
exactness at the fourth makes the first map of the *next* degree mono as soon as
`Hⁿ(U ⊓ V, F) = 0` again; in degree zero the monomorphism is
`Stacks.Cohomology.AmbientMayerVietoris.mono_ambientFirst_zero` instead.  So the pair map
`Hⁿ(W, F) ⟶ Hⁿ(U, F) ⊞ Hⁿ(V, F)` is an isomorphism in every degree, and `Hⁿ(V, F) = 0` makes
the projection onto the first summand one too; the composite of the two is the restriction map,
by `Stacks.Cohomology.AmbientMayerVietoris.ambientFirst_eq`.

Nothing here is specific to the cover being by two opens of a scheme: the statement is about an
arbitrary sheaf of rings on an arbitrary topological space, in the cohomology `Hgroup` of
Stacks 01E3.

## Main results

* `Stacks.Cohomology.AmbientMayerVietoris.isIso_ambientFirst_of_isZero`: the pair of restriction
  maps `Hⁿ(W, F) ⟶ Hⁿ(U, F) ⊞ Hⁿ(V, F)` is an isomorphism in every degree once the cohomology of
  `F` over the overlap `U ⊓ V` vanishes in every degree.
* `Stacks.Cohomology.AmbientMayerVietoris.isIso_HrestrictNT_app_of_isZero` and
  `Stacks.Cohomology.AmbientMayerVietoris.isIso_Hrestrict_of_isZero`: **excision**, in the two
  spellings of the restriction map.

## Implementation notes

The vanishing hypotheses are quantified over all degrees, which is what the two-sided use of the
overlap term forces: the monomorphism at degree `n + 1` and the epimorphism at degree `n` read
the same group `Hⁿ(U ⊓ V, F)`, so a bounded range of degrees would give the conclusion only in
the interior of that range.  For the intended application — a sheaf whose restriction to `V` is
a zero object — all degrees are available at once, so no sharper form is needed.

## References

* [Stacks Project, Tag 01EB](https://stacks.math.columbia.edu/tag/01EB)
* [Stacks Project, Tag 01E3](https://stacks.math.columbia.edu/tag/01E3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Cohomology.AmbientMayerVietoris

attribute [local instance 2000] CategoryTheory.Abelian.hasBinaryBiproducts
attribute [local instance]
  CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBinaryProducts

variable {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [EnoughInjectives (SheafOfModules.{u} O)]

variable (W U V : Opens X) (hU : U ≤ W) (hV : V ≤ W) (hUV : U ⊔ V = W)
  (F : SheafOfModules.{u} O)

/-! ### The pair of restrictions is an isomorphism -/

include hUV in
/-- **The pair of restriction maps is an epimorphism in degree `n` when the overlap carries no
degree-`n` cohomology.**  This is exactness of the Mayer--Vietoris sequence at
`Hⁿ(U, F) ⊞ Hⁿ(V, F)`, whose outgoing map lands in a zero object and is therefore zero. -/
public theorem epi_ambientFirst_of_isZero (n : ℕ) (hz : IsZero (Hgroup O (U ⊓ V) n F)) :
    Epi ((ambientFirst O W U V hU hV n).app F) :=
  (mayerVietorisAmbient_exact O W U V hU hV hUV n F).exact 0 |>.epi_f (hz.eq_zero_of_tgt _)

include hUV in
/-- **The pair of restriction maps is a monomorphism in degree `n + 1` when the overlap carries
no degree-`n` cohomology.**  This is exactness of the Mayer--Vietoris sequence at `Hⁿ⁺¹(W, F)`,
whose incoming connecting map starts at a zero object and is therefore zero. -/
public theorem mono_ambientFirst_of_isZero (n : ℕ) (hz : IsZero (Hgroup O (U ⊓ V) n F)) :
    Mono ((ambientFirst O W U V hU hV (n + 1)).app F) :=
  (mayerVietorisAmbient_exact O W U V hU hV hUV n F).exact 2 |>.mono_g (hz.eq_zero_of_src _)

include hUV in
/-- **The pair of restriction maps `Hⁿ(W, F) ⟶ Hⁿ(U, F) ⊞ Hⁿ(V, F)` is an isomorphism in every
degree** as soon as the cohomology of `F` over the overlap `U ⊓ V` vanishes in every degree.
Degree zero uses `Stacks.Cohomology.AmbientMayerVietoris.mono_ambientFirst_zero` for injectivity;
every higher degree uses the Mayer--Vietoris window one degree below. -/
public theorem isIso_ambientFirst_of_isZero (hz : ∀ n : ℕ, IsZero (Hgroup O (U ⊓ V) n F))
    (n : ℕ) : IsIso ((ambientFirst O W U V hU hV n).app F) := by
  have _ := epi_ambientFirst_of_isZero O W U V hU hV hUV F n (hz n)
  have _ : Mono ((ambientFirst O W U V hU hV n).app F) := by
    obtain _ | m := n
    · exact mono_ambientFirst_zero O W U V hU hV hUV F
    · exact mono_ambientFirst_of_isZero O W U V hU hV hUV F m (hz m)
  exact isIso_of_mono_of_epi _

/-- **A biproduct projection is an isomorphism when the other summand vanishes.**  The inverse is
the inclusion of the surviving summand: one triangle identity is
`Stacks.Cohomology.AmbientMayerVietoris.biprod_inl_fst_app` and the other is
`Stacks.Cohomology.AmbientMayerVietoris.biprod_total_app` with the second term killed. -/
public theorem isIso_biprod_fst_app_of_isZero (n : ℕ) (hz : IsZero (Hgroup O V n F)) :
    IsIso ((biprod.fst : Hfunctor O U n ⊞ Hfunctor O V n ⟶ Hfunctor O U n).app F) := by
  refine ⟨(biprod.inl : Hfunctor O U n ⟶ Hfunctor O U n ⊞ Hfunctor O V n).app F, ?_, ?_⟩
  · have ht := biprod_total_app (Hfunctor O U n) (Hfunctor O V n) F
    rw [hz.eq_zero_of_tgt ((biprod.snd : Hfunctor O U n ⊞ Hfunctor O V n ⟶
      Hfunctor O V n).app F), zero_comp, add_zero] at ht
    exact ht
  · exact biprod_inl_fst_app (Hfunctor O U n) (Hfunctor O V n) F

/-! ### Excision -/

include hV hUV in
/-- **Excision.**  Let `U ⊔ V = W` and let `F` be a sheaf of modules whose cohomology over `V`
and over `U ⊓ V` vanishes in every degree.  Then the restriction map
`Hⁿ(W, F) ⟶ Hⁿ(U, F)` is an isomorphism for every `n`: the piece `V` of the cover can be
excised.

The restriction map is the pair of restrictions followed by the projection onto the `U`-summand,
by `Stacks.Cohomology.AmbientMayerVietoris.ambientFirst_eq`, and both of those are isomorphisms
under the hypotheses. -/
public theorem isIso_HrestrictNT_app_of_isZero
    (hzV : ∀ n : ℕ, IsZero (Hgroup O V n F))
    (hzUV : ∀ n : ℕ, IsZero (Hgroup O (U ⊓ V) n F)) (n : ℕ) :
    IsIso ((HrestrictNT O hU n).app F) := by
  have hcomp : (ambientFirst O W U V hU hV n).app F ≫
      (biprod.fst : Hfunctor O U n ⊞ Hfunctor O V n ⟶ Hfunctor O U n).app F =
      (HrestrictNT O hU n).app F := by
    rw [← NatTrans.comp_app, ambientFirst_eq, biprod.lift_fst]
  have _ := isIso_ambientFirst_of_isZero O W U V hU hV hUV F hzUV n
  have _ := isIso_biprod_fst_app_of_isZero O U V F n (hzV n)
  rw [← hcomp]
  infer_instance

include hV hUV in
/-- **Excision, in the `Hrestrict` spelling.**  The restriction map on cohomology groups
`Hⁿ(W, F) ⟶ Hⁿ(U, F)` is an isomorphism in every degree once the cohomology of `F` over `V` and
over `U ⊓ V` vanishes in every degree. -/
public theorem isIso_Hrestrict_of_isZero
    (hzV : ∀ n : ℕ, IsZero (Hgroup O V n F))
    (hzUV : ∀ n : ℕ, IsZero (Hgroup O (U ⊓ V) n F)) (n : ℕ) :
    IsIso (Hrestrict O hU n F) :=
  isIso_HrestrictNT_app_of_isZero O W U V hU hV hUV F hzV hzUV n

end Stacks.Cohomology.AmbientMayerVietoris

end
