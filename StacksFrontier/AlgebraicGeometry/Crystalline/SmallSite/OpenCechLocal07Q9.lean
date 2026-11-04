module

public import StacksFrontier.AlgebraicGeometry.Crystalline.LevelFamilyFinality
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineGlobalNonempty
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.OpenCechSystem07Q9

/-!
# Local existence for the Čech system of an affine open

Fix a global crystalline situation `(p, (S, I, γ), X)`, affine opens `V ⊆ S` and `W ⊆ X` with `W`
mapping into `V`, and a surjective polynomial presentation of `Γ(W, ⊤)` over `Γ(V, ⊤)`.
`Crystalline.GlobalCrystallineSituation.SmallSite.openSystem07Q9` is the cosimplicial system
`(W, Spec D(n)/(p)^{N + e}, δ(n))` of that presentation, carried into `Cris(X/S)`.

This file proves that every object `(U, T, δ)` of `Cris(X/S)` with affine ambient scheme and with
`U` mapping into `W` admits a morphism to some level of the system in degree zero.  The object is
read in `Cris(W/S|_V)` (`CrystallineThickening.localObject`), its global sections are an object
`(Γ(T, ⊤), J, δ)` of the big affine crystalline category `CRIS(Γ(W, ⊤)/Γ(V, ⊤))`, which receives a
morphism from a finite level of the completed envelope by [Stacks, Tag 07HP], and `Spec` of that
morphism is the morphism wanted.  The object `U` need not be all of `W`: only a ring map
`Γ(W, ⊤) → Γ(T, ⊤)/J` is needed.

## Main definitions

* `specIsoInverseObj` — for `X` and `S` affine, the object of the chaotic subsite attached by the
  inverse of `wholeSiteEquivLittleAffine` to an object of `Cris(Γ(X, ⊤)/Γ(S, ⊤))` is `Spec` of it.

## Main results

* `exists_hom_to_wholeSpaceSystemOf_level` — for `X` and `S` affine, every object of `Cris(X/S)`
  with affine thickened scheme maps to a level of `wholeSpaceSystemOf` in degree zero.
* `exists_hom_to_openSystem07Q9_level` — every object of `Cris(X/S)` with affine ambient scheme
  lying over `W` maps to a level of `openSystem07Q9` in degree zero.

## References

* [Stacks Project, Tag 07HP](https://stacks.math.columbia.edu/tag/07HP)
* [Stacks Project, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Simplicial

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open Crystalline

section Presented

variable {S : GlobalCrystallineSituation.{u}} (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))
  [IsAffine S.X] [IsAffine S.S.scheme]

/-- **The inverse of `wholeSiteEquivLittleAffine` is `Spec`.**  For an object `L` of the little
affine crystalline category `Cris(Γ(X, ⊤)/Γ(S, ⊤))`, the object of the chaotic subsite `𝒞` which
the inverse equivalence attaches to it is isomorphic to `Spec L`, the object
`specWholeSpaceThickening` of `𝒞`: the two have isomorphic images under the equivalence, by
`wholeThickeningToAffineSpecIso`. -/
def specIsoInverseObj
    (L : _root_.Crystalline.CrystallineThickening.{u, u, u} (affineSituation S hp)) :
    ((wholeSiteEquivLittleAffine hp).inverse.obj L).unop ≅
      specWholeSpaceThickening hp L.obj L.property :=
  haveI : IsIso (specThickeningOfAffine hp L.obj).toX := isIso_specToX hp L.obj L.property
  (((wholeSiteEquivLittleAffine hp).unitIso.app (op (specWholeSpaceThickening hp L.obj
      L.property))) ≪≫ (wholeSiteEquivLittleAffine hp).inverse.mapIso
    ((affineIsCrystalline hp).fullyFaithfulι.preimageIso
      (wholeThickeningToAffineSpecIso hp L.obj))).unop

/-- **A morphism into `Spec` of an object of the little affine crystalline category, read as a
morphism into the object attached to it by the inverse equivalence.**  For an object `B` of
`Cris(X/S)` with affine thickened scheme and a morphism `φ : L ⟶ Γ(B)` of
`CRIS(Γ(X, ⊤)/Γ(S, ⊤))`, the morphism `B ⟶ Spec L` of `homOfAffineHom` followed by
`specIsoInverseObj`. -/
def homToInverseObj (B : CrystallineThickening S) [IsAffine B.obj.thickening.source]
    (L : _root_.Crystalline.CrystallineThickening.{u, u, u} (affineSituation S hp))
    (φ : L.obj ⟶ wholeThickeningToAffine hp B.obj) :
    B ⟶ (wholeι S).obj ((wholeSiteEquivLittleAffine hp).inverse.obj L).unop :=
  ObjectProperty.homMk (homOfAffineHom hp B.obj L.obj φ L.property) ≫
    (wholeι S).map (specIsoInverseObj hp L).inv

variable {ι : Type u}
  (g : MvPolynomial ι (affineSituation S hp).A →ₐ[(affineSituation S hp).A]
    (affineSituation S hp).C) (hg : Function.Surjective g)

/-- **[Stacks, Tag 07HP] on `Cris(X/S)`, for `X` and `S` affine and any presentation**: every
object of `Cris(X/S)` with affine thickened scheme admits a morphism to a level of the system
`wholeSpaceSystemOf` in degree zero.  The object need not lie over the whole of `X`. -/
theorem exists_hom_to_wholeSpaceSystemOf_level (B : CrystallineThickening S)
    [IsAffine B.obj.thickening.source] :
    ∃ e : ℕ, Nonempty (B ⟶ ((wholeSpaceSystemOf S hp g hg).obj (op ⦋0⦌)).obj e) := by
  classical
  obtain ⟨N, hN⟩ := exists_forall_le_levelThickening_hom
    (tensorPowerPresentation (affineSituation S hp) g 0)
    (tensorPowerPresentation_surjective _ _ hg 0)
    (tensorPowerEnvelopeThickening (affineSituation S hp) g hg 0)
    (wholeThickeningToAffine hp B.obj)
  refine ⟨max N (uniformLevel (affineSituation S hp)) - uniformLevel (affineSituation S hp), ?_⟩
  obtain ⟨h, ⟨φ⟩⟩ := hN (uniformLevel (affineSituation S hp) +
    (max N (uniformLevel (affineSituation S hp)) - uniformLevel (affineSituation S hp)))
    (by omega)
  exact ⟨homToInverseObj hp B _ φ⟩

end Presented

section Open

variable (S : GlobalCrystallineSituation.{u}) {V : S.S.scheme.Opens} {W : S.X.Opens}
  (hV : IsAffineOpen V) (hW : IsAffineOpen W) (hVW : W ≤ sourceToBase S ⁻¹ᵁ V) {ι : Type u}
  (g : MvPolynomial ι (openAffineSituation07Q9 S hW hVW).A →ₐ[(openAffineSituation07Q9 S hW hVW).A]
    (openAffineSituation07Q9 S hW hVW).C) (hg : Function.Surjective g)

/-- **Local existence for the Čech system of an affine open**: every object `(U, T, δ)` of
`Cris(X/S)` with affine ambient scheme and with `U` mapping into `W` admits a morphism to some
level of the transported system `openSystem07Q9` in degree zero.

The object is read in `Cris(W/S|_V)`, where it is
`Crystalline.GlobalCrystallineSituation.CrystallineThickening.localObject`; its thickened scheme
is affine, being closed in the affine ambient scheme; and there
`exists_hom_to_wholeSpaceSystemOf_level` applies.  Extending back gives the morphism, the
extension of the local reading being the object itself. -/
theorem exists_hom_to_openSystem07Q9_level (B : CrystallineThickening S)
    (hB : IsAffine B.obj.thickening.target.scheme)
    (hBW : Set.range B.obj.toX.base ⊆ (W : Set S.X)) :
    ∃ e : ℕ, Nonempty (B ⟶ ((openSystem07Q9 S hV hW hVW g hg).obj (op ⦋0⦌)).obj e) := by
  have := isAffine_restrictX07Q9 S hW hVW
  have := isAffine_restrictS07Q9 S hV hVW
  let B' := CrystallineThickening.localObject S V W hVW B hBW
  have : IsAffine B'.obj.thickening.source :=
    have := hB
    (IsClosedImmersion.isAffine_surjective_of_isAffine B.obj.thickening.immersion).1
  obtain ⟨e, ⟨φ⟩⟩ := exists_hom_to_wholeSpaceSystemOf_level
    (isNilpotent_prime_openSituation07Q9 S hW hVW) g hg B'
  exact ⟨e, ⟨(CrystallineThickening.extendLocalObjectIso S V W hVW B hBW).inv ≫
    (smallExtend S V W hVW).map φ⟩⟩

end Open

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
