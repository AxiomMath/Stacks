module

public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.BinaryProductPatch
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LevelRestrictionSurjectivity
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.SituationRestrict

/-!
# The Čech system of an affine open, transported to `Cris(X/S)`

Fix a global crystalline situation `(p, (S, I, γ), X)`, with neither `X` nor `S` affine, an
affine open `V ⊆ S` and an affine open `W ⊆ X` mapping into `V`.  The restricted situation
`(p, S|_V, W)` of `Crystalline.GlobalCrystallineSituation.restrict` has affine thickened space and
affine base, so the cosimplicial system `(W, Spec D(n)/(p)^{N + e}, δ(n))` of the proof of
[Stacks, Tag 07JN] can be formed for it.  Change of divided power base along the two open
immersions, `Crystalline.GlobalCrystallineSituation.smallExtend`, carries that system into
`Cris(X/S)`. The system is formed for an arbitrary surjective polynomial presentation, which at
the tautological presentation recovers
`Crystalline.GlobalCrystallineSituation.SmallSite.wholeSpaceSystem`.

## Main definitions

* `wholeSpaceSystemOf` — the system `(X, T(n)_e, δ(n))` for `X`, `S` affine and an arbitrary
  surjective polynomial presentation of `Γ(X, ⊤)` over `Γ(S, ⊤)`.
* `openAffineSituation07Q9` — the affine crystalline situation `(Γ(V, ⊤), Γ(W, ⊤))` of the
  restriction of the situation to the pair of affine opens `V ⊆ S`, `W ⊆ X`.
* `openSystem07Q9` — the system of the restricted situation, carried into `Cris(X/S)`.

## Main results

* `wholeSpaceSystemOf_canonicalPresentation` — at the tautological presentation the general
  construction is `wholeSpaceSystem`.
* `range_toX_openSystem07Q9` — the image in `X` of every object of the transported system is `W`.
* `isAffine_target_openSystem07Q9` — every object of the transported system has affine ambient
  scheme.
* `mono_openSystem07Q9_map` — the tower maps of the transported system are monomorphisms of
  `Cris(X/S)`.

## References

* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Tag 07KL](https://stacks.math.columbia.edu/tag/07KL)
* [Stacks Project, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Simplicial

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open Crystalline

/-! ### Monomorphisms of the small crystalline site -/

/-- A morphism of `Cris(X/S)` whose map of ambient schemes is a monomorphism is a monomorphism. -/
theorem mono_of_mono_targetHom {S : GlobalCrystallineSituation.{u}}
    {A A' : CrystallineThickening S} (t : A ⟶ A') (ht : Mono t.hom.targetHom.hom) : Mono t := by
  refine ⟨fun {B} a b hab ↦ ?_⟩
  have : IsOpenImmersion A.obj.toX := A.property
  refine ObjectProperty.hom_ext _ (Thickening.Hom.ext ?_ ?_)
  · refine (cancel_mono A.obj.toX).mp ?_
    rw [a.hom.toX_naturality, b.hom.toX_naturality]
  · refine DividedPowerScheme.Hom.ext ((cancel_mono t.hom.targetHom.hom).mp ?_)
    simpa [DividedPowerScheme.Hom.comp_hom] using
      congrArg (fun k : B.obj ⟶ A'.obj ↦ k.targetHom.hom) (congrArg (fun k ↦ k.hom) hab)

/-! ### The system `(X, T(n)_e, δ(n))` for an arbitrary presentation -/

section Presented

variable (S : GlobalCrystallineSituation.{u}) (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))
  [IsAffine S.X] [IsAffine S.S.scheme] {ι : Type u}
  (g : MvPolynomial ι (affineSituation S hp).A →ₐ[(affineSituation S hp).A]
    (affineSituation S hp).C) (hg : Function.Surjective g)

/-- The cosimplicial system of thickenings `(X, T(n)_e, δ(n))` of [Stacks, Tag 07JN] for a
surjective polynomial presentation `g` of `Γ(X, ⊤)` over `Γ(S, ⊤)`: in bidegree
`(n, e)` it is the object of `Cris(X/S)` corresponding, under the equivalence
`Crystalline.GlobalCrystallineSituation.wholeSiteEquivLittleAffine`, to the finite level
`D(n)/(p)^{N + e}` of the completed divided power envelope of the `(n + 1)`-fold tensor power of
`g`. -/
def wholeSpaceSystemOf : SimplicialObject (ℕ ⥤ CrystallineThickening S) :=
  ((affineLevelSystem (affineSituation S hp) g hg ⋙
      (Functor.whiskeringRight ℕᵒᵖ _ _).obj (affineToWholeSite S hp)) ⋙
    Functor.opInv ℕ (CrystallineThickening S)).leftOp

/-- At the tautological presentation the system is `wholeSpaceSystem`. -/
theorem wholeSpaceSystemOf_canonicalPresentation :
    wholeSpaceSystemOf S hp (canonicalPresentation _) (canonicalPresentation_surjective _) =
      wholeSpaceSystem S hp := rfl

/-- The object of the system in bidegree `(n, e)` is the transport of the finite level
`D(n)/(p)^{N + e}` across the affine-to-global equivalence. -/
theorem wholeSpaceSystemOf_obj_obj (n e : ℕ) :
    ((wholeSpaceSystemOf S hp g hg).obj (op ⦋n⦌)).obj e =
      (wholeι S).obj ((wholeSiteEquivLittleAffine hp).inverse.obj
        (((affineLevelSystem (affineSituation S hp) g hg).obj ⦋n⦌).obj (op e))).unop := rfl

/-- The tower maps of the system are the transports of the level drops
`D(n)/(p)^{N + e'} ⟶ D(n)/(p)^{N + e}`. -/
theorem wholeSpaceSystemOf_obj_map (n : ℕ) {e e' : ℕ} (h : e ≤ e') :
    ((wholeSpaceSystemOf S hp g hg).obj (op ⦋n⦌)).map (homOfLE h) =
      (wholeι S).map ((wholeSiteEquivLittleAffine hp).inverse.map
        (((affineLevelSystem (affineSituation S hp) g hg).obj ⦋n⦌).map
          ((homOfLE h).op : (op e' : ℕᵒᵖ) ⟶ op e))).unop := rfl

/-- The system consists of thickenings of the whole of `X`. -/
theorem isWholeSpaceSystem_wholeSpaceSystemOf :
    IsWholeSpaceSystem (wholeSpaceSystemOf S hp g hg) := fun n e ↦
  ((wholeSiteEquivLittleAffine hp).inverse.obj
    (((affineLevelSystem (affineSituation S hp) g hg).obj ⦋n⦌).obj (op e))).unop.property

/-- The tower maps of the system are closed immersions on ambient schemes. -/
theorem isClosedImmersion_wholeSpaceSystemOf_map (n : ℕ) {e e' : ℕ} (h : e ≤ e') :
    IsClosedImmersion
      (((wholeSpaceSystemOf S hp g hg).obj (op ⦋n⦌)).map (homOfLE h)).hom.targetHom.hom :=
  isClosedImmersion_targetHom_inverse_map hp _
    (surjective_hom_hom_affineLevelSystem_map g hg n h)

end Presented

/-! ### The restriction to a pair of affine opens -/

section Open

variable (S : GlobalCrystallineSituation.{u}) {V : S.S.scheme.Opens} {W : S.X.Opens}
  (hV : IsAffineOpen V) (hW : IsAffineOpen W) (hVW : W ≤ sourceToBase S ⁻¹ᵁ V)

include hW in
/-- The thickened space `W` of the restricted situation is affine. -/
theorem isAffine_restrictX07Q9 : IsAffine (restrict S V W hVW).X := hW

include hV in
/-- The divided power base `S|_V` of the restricted situation is affine. -/
theorem isAffine_restrictS07Q9 : IsAffine (restrict S V W hVW).S.scheme := hV

include hW in
/-- The prime is nilpotent on the global sections of the affine open `W`, the thickened space of
the restricted situation. -/
theorem isNilpotent_prime_openSituation07Q9 :
    IsNilpotent ((restrict S V W hVW).p : Γ((restrict S V W hVW).X, ⊤)) :=
  isNilpotent_prime_sections_of_isAffineOpen S W hW

/-- The affine crystalline situation `(Γ(V, ⊤), Γ(W, ⊤))` of a pair of affine opens: the affine
situation of the restriction of `S` to `V ⊆ S` and `W ⊆ X`. -/
abbrev openAffineSituation07Q9 : AffineCrystallineSituation.{u, u} :=
  affineSituation (restrict S V W hVW) (isNilpotent_prime_openSituation07Q9 S hW hVW)

variable {ι : Type u}
  (g : MvPolynomial ι (openAffineSituation07Q9 S hW hVW).A →ₐ[(openAffineSituation07Q9 S hW hVW).A]
    (openAffineSituation07Q9 S hW hVW).C) (hg : Function.Surjective g)

/-- The system of the restricted situation in `Cris(W/S|_V)`: `wholeSpaceSystemOf` for the
restriction of `S` to the affine opens `V` and `W`. -/
abbrev openLocalSystem07Q9 :
    SimplicialObject (ℕ ⥤ CrystallineThickening (restrict S V W hVW)) :=
  haveI := isAffine_restrictX07Q9 S hW hVW
  haveI := isAffine_restrictS07Q9 S hV hVW
  wholeSpaceSystemOf (restrict S V W hVW) (isNilpotent_prime_openSituation07Q9 S hW hVW) g hg

/-- The Čech system of the affine open `W`, transported to `Cris(X/S)`. In bidegree `(n, e)`
it is the object `(W, Spec D(n)/(p)^{N + e}, δ(n))` of `Cris(W/S|_V)` built from the presentation
`g` of `Γ(W, ⊤)` over `Γ(V, ⊤)`, read in `Cris(X/S)` by change of divided power base along the two
open immersions, [Stacks, Tag 07KL]. -/
def openSystem07Q9 : SimplicialObject (ℕ ⥤ CrystallineThickening S) :=
  openLocalSystem07Q9 S hV hW hVW g hg ⋙
    (Functor.whiskeringRight ℕ _ _).obj (smallExtend S V W hVW)

/-- The object of the transported system in bidegree `(n, e)` is the extension of the object of
the restricted system. -/
theorem openSystem07Q9_obj_obj (n e : ℕ) :
    ((openSystem07Q9 S hV hW hVW g hg).obj (op ⦋n⦌)).obj e =
      (smallExtend S V W hVW).obj (((openLocalSystem07Q9 S hV hW hVW g hg).obj (op ⦋n⦌)).obj e) :=
  rfl

/-- The tower maps of the transported system are the extensions of those of the restricted
system. -/
theorem openSystem07Q9_obj_map (n : ℕ) {e e' : ℕ} (h : e ≤ e') :
    ((openSystem07Q9 S hV hW hVW g hg).obj (op ⦋n⦌)).map (homOfLE h) =
      (smallExtend S V W hVW).map
        (((openLocalSystem07Q9 S hV hW hVW g hg).obj (op ⦋n⦌)).map (homOfLE h)) :=
  rfl

/-- Every object of the restricted system is a thickening of the whole of `W`. -/
theorem isIso_toX_openLocalSystem07Q9 (n e : ℕ) :
    IsIso (((openLocalSystem07Q9 S hV hW hVW g hg).obj (op ⦋n⦌)).obj e).obj.toX :=
  have := isAffine_restrictX07Q9 S hW hVW
  have := isAffine_restrictS07Q9 S hV hVW
  isWholeSpaceSystem_wholeSpaceSystemOf _ _ g hg n e

/-- The image in `X` of the thickened scheme of every object of the transported system is `W`. -/
theorem range_toX_openSystem07Q9 (n e : ℕ) :
    Set.range (((openSystem07Q9 S hV hW hVW g hg).obj (op ⦋n⦌)).obj e).obj.toX.base =
      (W : Set S.X) := by
  have := isIso_toX_openLocalSystem07Q9 S hV hW hVW g hg n e
  show Set.range ((((openLocalSystem07Q9 S hV hW hVW g hg).obj (op ⦋n⦌)).obj e).obj.toX ≫
    restrictXι S V W hVW).base = _
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    (ConcreteCategory.bijective_of_isIso
      (((openLocalSystem07Q9 S hV hW hVW g hg).obj (op ⦋n⦌)).obj e).obj.toX.base).2.range_eq,
    Set.image_univ, range_restrictXι]

/-- Every object of the transported system lies over `W`. -/
theorem range_toX_openSystem07Q9_subset (n e : ℕ) :
    Set.range (((openSystem07Q9 S hV hW hVW g hg).obj (op ⦋n⦌)).obj e).obj.toX.base ⊆
      (W : Set S.X) :=
  (range_toX_openSystem07Q9 S hV hW hVW g hg n e).le

/-- Every object of the transported system has affine ambient scheme. -/
theorem isAffine_target_openSystem07Q9 (n e : ℕ) :
    IsAffine
      (((openSystem07Q9 S hV hW hVW g hg).obj (op ⦋n⦌)).obj e).obj.thickening.target.scheme :=
  have := isAffine_restrictX07Q9 S hW hVW
  isAffine_target_of_isIso_toX (S := restrict S V W hVW) _
    (isIso_toX_openLocalSystem07Q9 S hV hW hVW g hg n e)

/-- The tower maps of the transported system are closed immersions on ambient schemes. -/
theorem isClosedImmersion_openSystem07Q9_map (n : ℕ) {e e' : ℕ} (h : e ≤ e') :
    IsClosedImmersion
      (((openSystem07Q9 S hV hW hVW g hg).obj (op ⦋n⦌)).map (homOfLE h)).hom.targetHom.hom :=
  have := isAffine_restrictX07Q9 S hW hVW
  have := isAffine_restrictS07Q9 S hV hVW
  isClosedImmersion_wholeSpaceSystemOf_map _ _ g hg n h

/-- The tower maps of the transported system are monomorphisms of `Cris(X/S)`. -/
theorem mono_openSystem07Q9_map (n : ℕ) {e e' : ℕ} (h : e ≤ e') :
    Mono (((openSystem07Q9 S hV hW hVW g hg).obj (op ⦋n⦌)).map (homOfLE h)) :=
  have := isClosedImmersion_openSystem07Q9_map S hV hW hVW g hg n h
  mono_of_mono_targetHom _ inferInstance

end Open

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
