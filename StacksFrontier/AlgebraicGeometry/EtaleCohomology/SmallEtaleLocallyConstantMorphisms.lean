module

public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantModules.Morphisms
import StacksCore.Tactic.StacksAttribute

/-!
# Morphisms of locally constant sheaves on the small étale site of a scheme

Let `X` be a scheme and let `φ : F ⟶ G` be a morphism of locally constant sheaves on
`X_étale`. If the source satisfies the appropriate finiteness condition — finite local
constancy for sheaves of sets and of abelian groups, finite-type local constancy for sheaves
of `R`-modules — then there is an étale covering on each member of which `φ` is the morphism of
constant sheaves attached to a map of sets, a homomorphism of abelian groups, or a homomorphism
of `R`-modules. This is Stacks 095C.

Each of the three parts is the Stacks 093S statement for an arbitrary site, specialised to the
small étale site; the source proves 095C exactly that way.

## Main results

* `Stacks.ConstantSheaf.exists_etaleCover_restrict_eq_constantSheaf_map` — part (1), sheaves of
  sets.
* `Stacks.ConstantSheaf.exists_etaleCover_restrict_eq_constantSheaf_map_abelian` — part (2),
  sheaves of abelian groups.
* `Stacks.ConstantSheaf.exists_etaleCover_restrict_eq_constantSheaf_map_modules` — part (3),
  sheaves of modules.

## Implementation notes

The statements are made over an arbitrary object `U` of the small étale site rather than only
over `X` itself, which is how the source phrases them; the source's version is the case of the
final object. This follows the general-site statements of Stacks 093S, which are proved in the
same form.

A sheaf of `R`-modules on `X_étale` is taken to be an object of
`Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{w} R)`, as everywhere else in this library
(compare the three parts of Tag 093Q and part (3) of Tag 03RW), and the finite-type condition
on the source is `Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant`: local constancy with
finitely generated constant values.

The abelian part carries one hypothesis the source does not state, `UnivLE.{u + 1, w}`, which
is a size condition relating the coefficient universe to the universe of the site; see the
implementation notes of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantAbelian.Morphisms` for why it is
there. The module part needs no such hypothesis, because a small étale site has fibre products.

## References

* [Stacks Project, Tag 095C](https://stacks.math.columbia.edu/tag/095C)
* [Stacks Project, Tag 093S](https://stacks.math.columbia.edu/tag/093S)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

universe w r u

namespace Stacks.ConstantSheaf

variable {X : Scheme.{u}}

/-- **Stacks 095C (1).** A morphism of locally constant sheaves of sets on the small étale site
of a scheme, whose source is finite locally constant, is on an étale covering of any object the
morphism of constant sheaves attached to a map of sets. -/
@[stacks 095C "sheaves of sets", sga "4 IX 2.1" "(i), étale site"]
lemma exists_etaleCover_restrict_eq_constantSheaf_map
    [∀ U : X.Etale, HasWeakSheafify ((smallEtaleTopology X).over U) (Type w)]
    (F G : Sheaf (smallEtaleTopology X) (Type w)) (φ : F ⟶ G)
    [IsFiniteLocallyConstant (smallEtaleTopology X) F]
    [IsLocallyConstant (smallEtaleTopology X) G] (U : X.Etale) :
    ∃ (I : Type (u + 1)) (V : I → X.Etale) (f : ∀ i, V i ⟶ U),
      Sieve.ofArrows V f ∈ smallEtaleTopology X U ∧ ∀ i,
        ∃ (A B : Type w), Finite A ∧
          ∃ (g : A ⟶ B)
            (eF : (constantSheaf ((smallEtaleTopology X).over (V i)) (Type w)).obj A ≅
              ((smallEtaleTopology X).overPullback (Type w) (V i)).obj F)
            (eG : (constantSheaf ((smallEtaleTopology X).over (V i)) (Type w)).obj B ≅
              ((smallEtaleTopology X).overPullback (Type w) (V i)).obj G),
              (constantSheaf ((smallEtaleTopology X).over (V i)) (Type w)).map g ≫ eG.hom =
                eF.hom ≫ ((smallEtaleTopology X).overPullback (Type w) (V i)).map φ :=
  exists_cover_restrict_eq_constantSheaf_map (smallEtaleTopology X) F G φ U

/-- **Stacks 095C (2).** A morphism of locally constant sheaves of abelian groups on the small
étale site of a scheme, whose source is finite locally constant, is on an étale covering of any
object the morphism of constant sheaves attached to a homomorphism of abelian groups. -/
@[stacks 095C "sheaves of abelian groups", sga "4 IX 2.1" "(ii) map, étale abelian"]
lemma exists_etaleCover_restrict_eq_constantSheaf_map_abelian [UnivLE.{u + 1, w}]
    [∀ U : X.Etale, HasWeakSheafify ((smallEtaleTopology X).over U) Ab.{w}]
    (F G : Sheaf (smallEtaleTopology X) Ab.{w}) (φ : F ⟶ G)
    [IsFiniteLocallyConstant (smallEtaleTopology X) F]
    [IsLocallyConstant (smallEtaleTopology X) G] (U : X.Etale) :
    ∃ (I : Type (u + 1)) (V : I → X.Etale) (f : ∀ i, V i ⟶ U),
      Sieve.ofArrows V f ∈ smallEtaleTopology X U ∧ ∀ i,
        ∃ (A B : Ab.{w}), Finite (A : Type w) ∧
          ∃ (g : A ⟶ B)
            (eF : (constantSheaf ((smallEtaleTopology X).over (V i)) Ab.{w}).obj A ≅
              ((smallEtaleTopology X).overPullback Ab.{w} (V i)).obj F)
            (eG : (constantSheaf ((smallEtaleTopology X).over (V i)) Ab.{w}).obj B ≅
              ((smallEtaleTopology X).overPullback Ab.{w} (V i)).obj G),
              (constantSheaf ((smallEtaleTopology X).over (V i)) Ab.{w}).map g ≫ eG.hom =
                eF.hom ≫ ((smallEtaleTopology X).overPullback Ab.{w} (V i)).map φ :=
  exists_cover_restrict_eq_constantSheaf_map_abelian (smallEtaleTopology X) F G φ U

/-- **Stacks 095C (3).** A morphism of locally constant sheaves of `R`-modules on the small
étale site of a scheme, whose source is locally constant of finite type, is on an étale covering
of any object the morphism of constant sheaves attached to a homomorphism of `R`-modules. -/
@[stacks 095C "sheaves of modules", sga "4 IX 2.1" "(ii) map, étale site"]
lemma exists_etaleCover_restrict_eq_constantSheaf_map_modules {R : Type r} [Ring R]
    [∀ U : X.Etale, HasWeakSheafify ((smallEtaleTopology X).over U) (ModuleCat.{w} R)]
    (F G : Sheaf (smallEtaleTopology X) (ModuleCat.{w} R)) (φ : F ⟶ G)
    (hF : IsFiniteTypeLocallyConstant R (smallEtaleTopology X) F)
    [IsLocallyConstant (smallEtaleTopology X) G] (U : X.Etale) :
    ∃ (I : Type (u + 1)) (V : I → X.Etale) (f : ∀ i, V i ⟶ U),
      Sieve.ofArrows V f ∈ smallEtaleTopology X U ∧ ∀ i,
        ∃ (A B : ModuleCat.{w} R), ModuleCat.isFG R A ∧
          ∃ (g : A ⟶ B)
            (eF : (constantSheaf ((smallEtaleTopology X).over (V i)) (ModuleCat.{w} R)).obj A ≅
              ((smallEtaleTopology X).overPullback (ModuleCat.{w} R) (V i)).obj F)
            (eG : (constantSheaf ((smallEtaleTopology X).over (V i)) (ModuleCat.{w} R)).obj B ≅
              ((smallEtaleTopology X).overPullback (ModuleCat.{w} R) (V i)).obj G),
              (constantSheaf ((smallEtaleTopology X).over (V i)) (ModuleCat.{w} R)).map g ≫
                  eG.hom =
                eF.hom ≫ ((smallEtaleTopology X).overPullback (ModuleCat.{w} R) (V i)).map φ :=
  exists_cover_restrict_eq_constantSheaf_map_modules_of_hasPullbacks
    (smallEtaleTopology X) F G φ hF U

end Stacks.ConstantSheaf

end
