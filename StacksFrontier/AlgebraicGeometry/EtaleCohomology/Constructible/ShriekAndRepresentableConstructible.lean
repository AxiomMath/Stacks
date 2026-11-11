module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.AbelianShriekConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ShriekFiniteModuleConstructible
public import StacksCore.Tactic.StacksAttribute

/-!
# Tag 03S8 in one statement

Let `X` be a quasi-compact and quasi-separated scheme of a big étale site and `U` a quasi-compact
quasi-separated object of its small étale site, so that `U ⟶ X` is an étale morphism of
quasi-compact quasi-separated schemes. Tag 03S8 asserts three constructibility statements:

1. the sheaf of sets represented by `U` is constructible;
2. the extension by zero of the constant abelian sheaf at a finite abelian group is a
   constructible abelian sheaf; and
3. the extension by zero of the constant sheaf at a finite module over a Noetherian ring is a
   constructible sheaf of modules.

Each part is already a theorem of this library, stating that part alone. This file conjoins the
three into the single statement of the tag, forwarding each conjunct to the theorem that proves
it; the single-part registrations of the tag are kept.

## Main results

* `isConstructible_sheafifiedYoneda_and_abelianShriekConstant_and_moduleShriek_of_qcqs`: the
  conjunction of the three constructibility statements above.

## Implementation notes

This file exists so that the conjunction can be stated without the instance assumptions its
components carry. Parts (2) and (3) are proved in files whose `variable` blocks assume two
families each of `CategoryTheory.Functor.IsRightAdjoint` for small étale pushforward and of
`CategoryTheory.HasWeakSheafify` for the slices, with coefficients in `AddCommGrpCat.{u + 1}` and
in `ModuleCat.{u + 1} R` respectively; Lean includes those assumptions in the elaborated
signature of every declaration there, so the components appear conditional on them. At the
coefficient universes the two parts actually use, all four families are inferable, so stating the
conjunction outside those `variable` blocks lets instance synthesis discharge them and leaves a
statement carrying only the source's own hypotheses.

## References

* [Stacks Project, Tag 03S8](https://stacks.math.columbia.edu/tag/03S8)
* [Stacks Project, Tag 03S0](https://stacks.math.columbia.edu/tag/03S0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

attribute [local instance 2000] Sheaf.instHasColimitsOfShape Sheaf.instHasFiniteCoproducts

/-- **Stacks 03S8.** Let `X` be a quasi-compact and quasi-separated scheme of a big étale site,
`R` a Noetherian commutative ring and `U` a quasi-compact quasi-separated object of the small
étale site of `X`, so that `j : U ⟶ X` is an étale morphism of quasi-compact quasi-separated
schemes. Then

1. the sheaf `h_U^#` of sets represented by `U` is a constructible sheaf of sets on `X_étale`;
2. for every finite abelian group `M` the extension by zero `j_!\underline{M}` is a constructible
   abelian sheaf on `X_étale`; and
3. for every finite `R`-module `M` the extension by zero `j_{U!}\underline{M}` is a constructible
   sheaf of `R`-modules on `X_étale`.

This is the whole tag in one statement, under the source's quasi-compactness and
quasi-separatedness of `X` and of `U` and no other hypothesis. Each part is proved by the theorem
that states it alone: `AlgebraicGeometry.isConstructibleSetSheaf_sheafifiedYoneda_of_qcqs` for
part (1), `AlgebraicGeometry.isConstructibleAbelianSheaf_abelianShriekConstant` for part (2), and
`AlgebraicGeometry.isConstructibleModuleSheaf_moduleShriek` for part (3). The other registrations
of the tag each state one part, or a case of one, without further hypotheses.

The ring `R`, its commutativity and its Noetherianness are hypotheses of part (3) alone: parts
(1) and (2) do not mention `R` and are proved without it. Part (1) is used in proving parts (2)
and (3), so the conjunction asserts no more than parts (2) and (3) together do; it is the
statement of the tag rather than a new fact.

No instance beyond the source's hypotheses is assumed, although the components appear to assume
four families of them; see the implementation notes above. -/
@[stacks 03S8 "the whole tag: part (1) the sheaf of sets represented by a quasi-compact \
quasi-separated etale object is constructible, part (2) an extension by zero of the constant \
sheaf at a finite abelian group is a constructible abelian sheaf, part (3) an extension by zero \
of the constant sheaf at a finite module over a Noetherian commutative ring is a constructible \
sheaf of modules. Assumed, as in the source: quasi-compactness and quasi-separatedness of \
X and of U, and for part (3) a Noetherian commutative ring. No IsRightAdjoint or HasWeakSheafify \
assumption is carried, those instances being inferred here. The single-part registrations of \
the tag are kept beside it."]
public theorem isConstructible_sheafifiedYoneda_and_abelianShriekConstant_and_moduleShriek_of_qcqs
    (B : BigEtaleSite.{u}) (X : B.Scheme) (R : Type (u + 1)) [CommRing R] [IsNoetherianRing R]
    [CompactSpace X.obj] [QuasiSeparatedSpace X.obj] (U : SmallEtale B X.obj X.property)
    [CompactSpace U.obj.left.obj] [QuasiSeparatedSpace U.obj.left.obj] :
    IsConstructibleSetSheaf B X
        ((Sheaf.sheafifiedYoneda (SmallEtale.topology B X.obj X.property)).obj U) ∧
      (∀ (M : AddCommGrpCat.{u + 1}) [Finite M],
        IsConstructibleAbelianSheaf B X
          ((abelianExtensionByZero B X.obj X.property U).obj
            ((constantSheaf (SmallEtale.topology B U.obj.left.obj U.obj.left.property)
              AddCommGrpCat.{u + 1}).obj M))) ∧
      (∀ (M : ModuleCat.{u + 1} R) [Module.Finite R M],
        IsConstructibleModuleSheaf B X R (moduleShriek.{u, u + 1, u + 1} B X R U M)) :=
  ⟨isConstructibleSetSheaf_sheafifiedYoneda_of_qcqs B X U,
    fun M _ => isConstructibleAbelianSheaf_abelianShriekConstant B X M U,
    fun M _ => isConstructibleModuleSheaf_moduleShriek B X R U M⟩

end AlgebraicGeometry

end
