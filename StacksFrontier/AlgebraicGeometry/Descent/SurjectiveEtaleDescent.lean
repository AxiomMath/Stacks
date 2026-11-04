module

public import StacksFrontier.AlgebraicGeometry.Descent.MorphismProperty.LocalFiniteness
public import StacksFrontier.AlgebraicGeometry.Etale.Descent
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Permanence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Descent along a surjective étale morphism of sources

Consider morphisms of schemes `X ⟶ Y ⟶ Z` whose first factor is surjective and étale. Such a
factor is in particular surjective, flat and locally of finite presentation, so the fppf
descent of Tag 02KL applies to it, and this file records the three properties whose descent
along it the étale-locality machinery and the theory of algebraic spaces both need:
étaleness, local finite type, and local finite type together with local quasi-finiteness.

All three statements are about morphisms of *schemes*. They are collected here rather than
next to the fppf descent of Tag 02KL because each of them also needs an ingredient that the
pure fppf descent does not — Tag 02K6 for étaleness and Tag 0GWS for quasi-finiteness — and
because their consumers lie in two directions which may not depend on one another: the
étale-locality criteria under `StacksDraft.AlgebraicGeometry.Descent.EtaleLocal`, and the
base-change theorems for algebraic spaces under `StacksDraft.AlgebraicGeometry.Spaces`.

## Main definitions

There are no new definitions.

## Main results

* `Stacks.Etale.etale_of_comp_surjective_etale`: **Stacks 02KM**, étale case — étaleness
  descends.
* `AlgebraicGeometry.locallyOfFiniteType_of_comp_surjective_etale`: local finite type
  descends.
* `AlgebraicGeometry.locallyQuasiFinite_of_comp_surjective_etale`: local finite type
  together with local quasi-finiteness descends.

## Implementation notes

In the two property-descent statements the three hypotheses `Surjective α`, `Etale α` and the
property of the composite are taken as explicit arguments rather than as instances, because
the criteria of `StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.ZariskiToEtale` ask for that
form; each proof re-installs them as instances with `have` and then appeals to the
instance-form lemma. Tag 02KM itself takes them as instances, which is how its consumers —
étale charts of algebraic spaces, and the étale-local criteria through a wrapper — have
them.

The quasi-finite statement descends the *conjunction* of local finite type and local
quasi-finiteness, not local quasi-finiteness alone: Tag 0GWS needs the descended morphism to
be locally of finite type already, and that is exactly what the finite-type half of the
conjunction supplies.

## References

* [Stacks Project, Tag 02K6](https://stacks.math.columbia.edu/tag/02K6)
* [Stacks Project, Tag 02KL](https://stacks.math.columbia.edu/tag/02KL)
* [Stacks Project, Tag 0GWS](https://stacks.math.columbia.edu/tag/0GWS)
-/

@[expose] public section

open CategoryTheory

universe u

namespace Stacks.Etale

open AlgebraicGeometry

/-- **Stacks 02KM**, étale case. If `f : X ⟶ Y` is surjective and étale and the composite
`f ≫ q` is étale, then `q : Y ⟶ S` is étale.

The missing hypothesis of Tag 02K6, that `q` be locally of finite presentation, follows from
Tag 02KL: `f` is surjective, flat and locally of finite presentation, and `f ≫ q` is locally
of finite presentation because it is étale. -/
@[stacks 02KM "etale_case", ega "IV 17.7.5" "special case"]
theorem etale_of_comp_surjective_etale {X Y S : Scheme.{u}}
    (f : X ⟶ Y) (q : Y ⟶ S) [Surjective f] [Etale f] [Etale (f ≫ q)] :
    Etale q :=
  have : LocallyOfFinitePresentation q := locallyOfFinitePresentation_of_comp_of_fppf f q
  etale_of_comp_surjective_etale_of_locallyOfFinitePresentation f q

end Stacks.Etale

namespace AlgebraicGeometry

/-- Local finite type of a morphism of schemes descends along a surjective étale morphism of
sources: it is `AlgebraicGeometry.locallyOfFiniteType_of_comp_of_fppf`, an étale morphism
being flat and locally of finite presentation. -/
theorem locallyOfFiniteType_of_comp_surjective_etale {T₁ T₂ T₃ : Scheme.{u}}
    (α : T₁ ⟶ T₂) (k : T₂ ⟶ T₃) (hs : Surjective α) (het : Etale α)
    (hαk : LocallyOfFiniteType (α ≫ k)) :
    LocallyOfFiniteType k :=
  have : Surjective α := hs
  have : Etale α := het
  have : LocallyOfFiniteType (α ≫ k) := hαk
  locallyOfFiniteType_of_comp_of_fppf α k

/-- Local quasi-finiteness of a morphism of schemes, in the sense of the Stacks Project,
descends along a surjective étale morphism of sources: the finite-type factor is
`AlgebraicGeometry.locallyOfFiniteType_of_comp_of_fppf` and the fibrewise factor is Tag
0GWS, `AlgebraicGeometry.locallyQuasiFinite_of_comp_surjective`, whose finite-type hypothesis
on the descended morphism the first factor supplies. -/
theorem locallyQuasiFinite_of_comp_surjective_etale {T₁ T₂ T₃ : Scheme.{u}}
    (α : T₁ ⟶ T₂) (k : T₂ ⟶ T₃) (hs : Surjective α) (het : Etale α)
    (hαk : ((@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
      (@LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u})) (α ≫ k)) :
    ((@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
      (@LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u})) k :=
  have hft : LocallyOfFiniteType k := locallyOfFiniteType_of_comp_surjective_etale α k hs het hαk.1
  have : Surjective α := hs
  have : LocallyQuasiFinite (α ≫ k) := hαk.2
  ⟨hft, locallyQuasiFinite_of_comp_surjective α k⟩

end AlgebraicGeometry

end
