module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Crystalline.Scheme

/-!
# Closed fibres of divided power schemes

Let `(X, I, γ)` be a divided power scheme.  Because `I` is a quasi-coherent sheaf of ideals it
cuts out a closed subscheme `X₀ = V(I)` of `X`, the *closed fibre* of the divided power scheme.
A morphism `f : (X, I, γ) ⟶ (Y, J, δ)` of divided power schemes carries `J` into `I` on sections,
so the composite `X₀ ⟶ X ⟶ Y` kills `J` and therefore factors uniquely through `Y₀`; the closed
fibre is thus a functor on divided power schemes.

The results are stated for an arbitrary *presentation* of the closed fibre: a
`Crystalline.DividedPowerScheme.ClosedFiberPresentation X` is a scheme together with a closed
immersion into `X` whose ideal is, on sections, the divided power ideal of `X`. Any two
presentations of the same divided power scheme are canonically isomorphic
(`ClosedFiberPresentation.isoOfPresentations`), so the induced map on closed fibres
(`ClosedFiberPresentation.map`) and its defining equation do not depend on the presentation.

## Main definitions

* `Crystalline.DividedPowerScheme.ClosedFiberPresentation` — a scheme with a closed immersion
  into the underlying scheme of a divided power scheme, cutting out the divided power ideal.
* `Crystalline.DividedPowerScheme.ClosedFiberPresentation.map` — the map on closed fibres induced
  by a morphism of divided power schemes, bundled with its defining equation.
* `Crystalline.DividedPowerScheme.ClosedFiberPresentation.isoOfPresentations` — the canonical
  isomorphism between two presentations of the same closed fibre.
* `Crystalline.DividedPowerScheme.ClosedFiberPresentation.pullbackComparison` — for a commuting
  square of divided power schemes, the comparison from the closed fibre of its vertex to the
  fibre product of the closed fibres, bundled with its two projection equations.

## Main results

* `ClosedFiberPresentation.ker_le_ker` — the kernel of the closed fibre of the target is
  contained in the kernel of `X₀ ⟶ X ⟶ Y`.
* `ClosedFiberPresentation.subsingleton_factorizations` — the factorization is unique.
* `ClosedFiberPresentation.map_id` and `ClosedFiberPresentation.map_comp` — functoriality.
* `ClosedFiberPresentation.ker_eq` — two presentations of the same divided power scheme have the
  same ideal sheaf, hence are canonically isomorphic.

## Implementation notes

The closed subscheme cut out by the divided power ideal (Stacks 01IN) is not constructed in the
library, which is why the results take a presentation of the closed fibre as input.

## References

* [Stacks Project, Tag 07ME](https://stacks.math.columbia.edu/tag/07ME)
* [Stacks Project, Tag 01IN](https://stacks.math.columbia.edu/tag/01IN)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace Crystalline.DividedPowerScheme

/-- A presentation of the closed fibre of a divided power scheme `X`: a scheme `carrier` together
with a closed immersion `ι` into the underlying scheme of `X` whose ideal is the divided power
ideal of `X`.  The two conditions say that `ι` kills every section of the divided power ideal, and
that over an affine open it kills nothing else. -/
public structure ClosedFiberPresentation (X : DividedPowerScheme.{u}) where
  /-- The underlying scheme of the closed fibre. -/
  carrier : Scheme.{u}
  /-- The canonical inclusion of the closed fibre. -/
  ι : carrier ⟶ X.scheme
  /-- The inclusion is a closed immersion. -/
  isClosedImmersion : IsClosedImmersion ι
  /-- Every section of the divided power ideal dies on the closed fibre. -/
  app_eq_zero_of_mem (V : X.scheme.Opens) (s : Γ(X.scheme, V))
    (hs : s ∈ sectionIdeal X.scheme.sheaf X.ideal (op V)) : (ι.app V).hom s = 0
  /-- Over an affine open, a section dying on the closed fibre lies in the divided power ideal. -/
  mem_of_app_eq_zero (V : X.scheme.affineOpens) (s : Γ(X.scheme, V.1))
    (hs : (ι.app V.1).hom s = 0) : s ∈ sectionIdeal X.scheme.sheaf X.ideal (op V.1)

attribute [instance] ClosedFiberPresentation.isClosedImmersion

namespace ClosedFiberPresentation

variable {X Y Z : DividedPowerScheme.{u}}

/-- Over an affine open, the sections dying on the closed fibre are exactly the sections of the
divided power ideal. -/
public theorem app_eq_zero_iff (P : ClosedFiberPresentation X) (V : X.scheme.affineOpens)
    (s : Γ(X.scheme, V.1)) :
    (P.ι.app V.1).hom s = 0 ↔ s ∈ sectionIdeal X.scheme.sheaf X.ideal (op V.1) :=
  ⟨P.mem_of_app_eq_zero V s, P.app_eq_zero_of_mem V.1 s⟩

/-- The ideal sheaf of a presentation of the closed fibre is the ideal sheaf determined by the
divided power ideal; in particular it does not depend on the presentation. -/
public theorem ker_eq_ofIdeals (P : ClosedFiberPresentation X) :
    P.ι.ker = Scheme.IdealSheafData.ofIdeals
      (fun V : X.scheme.affineOpens => sectionIdeal X.scheme.sheaf X.ideal (op V.1)) := by
  refine congrArg Scheme.IdealSheafData.ofIdeals (funext fun V => ?_)
  refine SetLike.ext fun s => ?_
  rw [RingHom.mem_ker]
  exact P.app_eq_zero_iff V s

/-- Two presentations of the closed fibre of the same divided power scheme have the same ideal
sheaf. -/
public theorem ker_eq (P P' : ClosedFiberPresentation X) : P.ι.ker = P'.ι.ker := by
  rw [P.ker_eq_ofIdeals, P'.ker_eq_ofIdeals]

/-- For a morphism `f` of divided power schemes, the ideal sheaf of the closed fibre of the target
is contained in the kernel of the composite `X₀ ⟶ X ⟶ Y`. -/
public theorem ker_le_ker (P : ClosedFiberPresentation X) (Q : ClosedFiberPresentation Y)
    (f : X ⟶ Y) : Q.ι.ker ≤ (P.ι ≫ f.hom).ker := by
  rw [show (P.ι ≫ f.hom).ker = Scheme.IdealSheafData.ofIdeals
        (fun V : Y.scheme.affineOpens => RingHom.ker ((P.ι ≫ f.hom).app V.1).hom) from rfl,
    Scheme.IdealSheafData.le_ofIdeals_iff]
  intro U s hs
  rw [RingHom.mem_ker, Scheme.Hom.comp_app]
  exact P.app_eq_zero_of_mem _ _
    (DividedPowerScheme.Hom.ideal_comp f U.1
      (Ideal.mem_map_of_mem _ (Q.mem_of_app_eq_zero U s (Q.ι.ideal_ker_le U hs))))

/-- The map on closed fibres induced by a morphism of divided power schemes, together with its
defining equation. -/
public def map (P : ClosedFiberPresentation X) (Q : ClosedFiberPresentation Y) (f : X ⟶ Y) :
    {g : P.carrier ⟶ Q.carrier // g ≫ Q.ι = P.ι ≫ f.hom} :=
  ⟨IsClosedImmersion.lift Q.ι (P.ι ≫ f.hom) (P.ker_le_ker Q f),
    IsClosedImmersion.lift_fac _ _ _⟩

/-- The induced map on closed fibres commutes with the inclusions. -/
@[reassoc (attr := simp)]
public theorem map_comp_ι (P : ClosedFiberPresentation X) (Q : ClosedFiberPresentation Y)
    (f : X ⟶ Y) : (P.map Q f).1 ≫ Q.ι = P.ι ≫ f.hom :=
  (P.map Q f).2

/-- A factorization of `X₀ ⟶ X ⟶ Y` through the closed fibre of `Y` is unique. -/
public theorem subsingleton_factorizations (P : ClosedFiberPresentation X)
    (Q : ClosedFiberPresentation Y) (f : X ⟶ Y) :
    Subsingleton {g : P.carrier ⟶ Q.carrier // g ≫ Q.ι = P.ι ≫ f.hom} :=
  ⟨fun g g' => Subtype.ext ((cancel_mono Q.ι).mp (g.2.trans g'.2.symm))⟩

/-- The identity of a divided power scheme induces the identity on a closed fibre. -/
@[simp]
public theorem map_id (P : ClosedFiberPresentation X) : (P.map P (𝟙 X)).1 = 𝟙 P.carrier := by
  rw [← cancel_mono P.ι, map_comp_ι, DividedPowerScheme.Hom.id_hom, Category.comp_id,
    Category.id_comp]

/-- The closed fibre is functorial in the divided power scheme. -/
public theorem map_comp (P : ClosedFiberPresentation X) (Q : ClosedFiberPresentation Y)
    (R : ClosedFiberPresentation Z) (f : X ⟶ Y) (g : Y ⟶ Z) :
    (P.map R (f ≫ g)).1 = (P.map Q f).1 ≫ (Q.map R g).1 := by
  rw [← cancel_mono R.ι, Category.assoc, map_comp_ι, map_comp_ι, ← Category.assoc, map_comp_ι,
    DividedPowerScheme.Hom.comp_hom, Category.assoc]

/-- Two presentations of the closed fibre of the same divided power scheme are canonically
isomorphic over the ambient scheme. -/
public def isoOfPresentations (P P' : ClosedFiberPresentation X) : P.carrier ≅ P'.carrier :=
  letI : IsIso (IsClosedImmersion.lift P'.ι P.ι (P'.ker_eq P).le) :=
    IsClosedImmersion.isIso_lift P'.ι P.ι (P'.ker_eq P)
  asIso (IsClosedImmersion.lift P'.ι P.ι (P'.ker_eq P).le)

/-- The canonical isomorphism of two presentations of a closed fibre commutes with their
inclusions. -/
@[reassoc (attr := simp)]
public theorem isoOfPresentations_hom_comp_ι (P P' : ClosedFiberPresentation X) :
    (P.isoOfPresentations P').hom ≫ P'.ι = P.ι :=
  IsClosedImmersion.lift_fac _ _ _

section Comparison

variable {S T T' W : DividedPowerScheme.{u}}

/-- A commuting square of divided power schemes induces a map from the closed fibre of its vertex
to the fibre product of the closed fibres, characterized by its two projection equations. -/
public def pullbackComparison (PS : ClosedFiberPresentation S) (PT : ClosedFiberPresentation T)
    (PT' : ClosedFiberPresentation T') (PW : ClosedFiberPresentation W)
    {f : T ⟶ S} {f' : T' ⟶ S} {p : W ⟶ T} {p' : W ⟶ T'} (hp : p ≫ f = p' ≫ f') :
    {c : PW.carrier ⟶ Limits.pullback (PT.map PS f).1 (PT'.map PS f').1 //
      c ≫ Limits.pullback.fst (PT.map PS f).1 (PT'.map PS f').1 = (PW.map PT p).1 ∧
        c ≫ Limits.pullback.snd (PT.map PS f).1 (PT'.map PS f').1 = (PW.map PT' p').1} :=
  ⟨Limits.pullback.lift (PW.map PT p).1 (PW.map PT' p').1
      (by rw [← map_comp, ← map_comp, hp]),
    Limits.pullback.lift_fst _ _ _, Limits.pullback.lift_snd _ _ _⟩

end Comparison

end ClosedFiberPresentation

end Crystalline.DividedPowerScheme

end
