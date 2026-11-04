module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.Functoriality
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ZariskiToposMorphism

/-!
# The inverse image under `u_{X/S}` of the sheaf represented by an open of `X`

Let `W` be an open of `X` and let `h_W` be the sheaf on the small Zariski site of `X` that it
represents.  This file computes `u_{X/S}^{-1}h_W`, where `u_{X/S} : (X/S)_cris ⟶ Sh(X_Zar)` is the
morphism of topoi of [Stacks, Tag 07IL]: its sections over an object `(U, T, δ)` of `Cris(X/S)`
are a singleton if the open image of `U` in `X` is contained in `W`, and empty otherwise.

This is the computation that clause (d) of [Stacks, Tag 07KL] needs, and it is *not* an instance
of [Stacks, Tag 04D3].  That tag computes `f^{-1}h_V^#` for a morphism of topoi presented by a
**continuous** functor of sites, where the inverse image is restriction; `u_{X/S}` is presented by
the **cocontinuous** `forgetToOpens`, whose inverse image
`CategoryTheory.Functor.sheafPullbackCocontinuous` restricts *and then sheafifies*, and Mathlib's
`CategoryTheory.Functor.IsContinuous` is not available for `forgetToOpens`.  Two general routes to
it exist and neither applies: one needs pullbacks in `Cris(X/S)`, which that site does not have,
and the other needs a right adjoint, as in
`...SmallSite.forgetToOpensClosedFiberAdjunction.isContinuous_of_isCocontinuous` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/ClosedFiberCofinal.lean`, which is available
only for the closed fibre and only when `I` is locally nilpotent.

The sheafification is nevertheless harmless here, and that is the content of the file: the
restriction `(U, T, δ) ↦ h_W(U)` is *already* a sheaf on `Cris(X/S)`.  Its values are
subsingletons, so the sheaf condition is the single implication that if every member of a covering
sieve of `(U, T, δ)` has its open image inside `W`, then so does `(U, T, δ)`.  By
`CategoryTheory.Precoverage.isSheaf_toGrothendieck_iff` this only has to be checked for the
pullbacks of the *generating* Zariski covering families, and a Zariski covering family of
`(U, T, δ)` pulled back along `(U', T', δ') ⟶ (U, T, δ)` is refined by the restrictions of
`(U', T', δ')` to the preimages of the ambient opens — which is exactly the refinement already
used to prove cocontinuity of change of divided power base,
`GlobalCrystallineSituation.smallChangeBase_functorPullback_pullback_mem_smallTopology`.
So no pullback in `Cris(X/S)` is needed: the opens are pulled back on ambient schemes.

The resulting sheaf is a subobject of the final sheaf — an "open subobject" in the sense of the
remark of [Stacks, Tag 07ML] — because `h_W` is one and the inverse image is left exact.

Taking `W` to be the open image of `g : X' ⟶ X`, the last result of the file identifies the
objects on which `u_{X/S}^{-1}h_{X'}` has a section with the essential image of change of divided
power base, `Crystalline.GlobalCrystallineSituation.smallChangeBase_essImage_iff`.  That is the
statement that the site of elements of `u_{X/S}^{-1}h_{X'}` is the full subcategory of `Cris(X/S)`
cut out by `Cris(X'/S')`, which is the category-level half of clause (d).

## Main definitions

* `Crystalline.GlobalCrystallineSituation.opensRepr` — `h_W`, the presheaf on `X_Zar` represented
  by an open `W` of `X`, with its values lifted to the coefficient universe `Type (u + 1)` of the
  crystalline topos.
* `Crystalline.GlobalCrystallineSituation.opensReprSheaf` — the same, as a sheaf.
* `Crystalline.GlobalCrystallineSituation.zariskiInverseImageOpensReprIso` — the identification of
  `u_{X/S}^{-1}h_W` with the restriction `(U, T, δ) ↦ h_W(U)`, the sheafification being trivial.

## Main results

* `Crystalline.GlobalCrystallineSituation.forgetToOpens_generate_pullback_functorPushforward_mem`
  — the images in `X_Zar` of the pullback of a Zariski covering sieve cover.
* `Crystalline.GlobalCrystallineSituation.isSheaf_forgetToOpensOpCompOpensRepr` — the restriction
  of `h_W` along `forgetToOpens` is already a sheaf on `Cris(X/S)`.
* `Crystalline.GlobalCrystallineSituation.nonempty_zariskiInverseImage_opensRepr_iff` — the
  sections of `u_{X/S}^{-1}h_W` over `(U, T, δ)`: nonempty exactly when the open image of `U` in
  `X` lies in `W`, and always a subsingleton.
* `Crystalline.GlobalCrystallineSituation.nonempty_zariskiInverseImage_opensRepr_iff_essImage` —
  for `W` the open image of `X' ⟶ X`, those are the objects of `Cris(X/S)` that come from
  `Cris(X'/S')`.

## References

* [Stacks Project, Tag 07KL](https://stacks.math.columbia.edu/tag/07KL)
* [Stacks Project, Tag 07IL](https://stacks.math.columbia.edu/tag/07IL)
* [Stacks Project, Tag 04D3](https://stacks.math.columbia.edu/tag/04D3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe w v u

namespace Crystalline.GlobalCrystallineSituation

/-- **A presheaf with subsingleton values is a sheaf for a presieve as soon as a family of
elements for that presieve produces a section over the base.**  Both halves of the amalgamation
condition are equalities in a subsingleton. -/
theorem isSheafFor_of_subsingleton {C : Type u} [Category.{v} C] {P : Cᵒᵖ ⥤ Type w}
    (hsub : ∀ X : Cᵒᵖ, Subsingleton (P.obj X)) {X : C} (R : Presieve X)
    (hne : Presieve.FamilyOfElements P R → Nonempty (P.obj (op X))) :
    Presieve.IsSheafFor P R := fun x _ ↦
  ⟨(hne x).some, fun _ _ _ ↦ (hsub _).elim _ _, fun _ _ ↦ (hsub _).elim _ _⟩

variable {S : GlobalCrystallineSituation.{u}}

/-- **The sheaf `h_W` on the small Zariski site of `X` represented by an open `W`**, with its
values lifted from the universe of the morphisms of `X_Zar` to the coefficient universe
`Type (u + 1)` of the crystalline topos. -/
def opensRepr (W : S.X.Opens) : (S.X.Opens)ᵒᵖ ⥤ Type (u + 1) :=
  yoneda.obj W ⋙ uliftFunctor.{u + 1}

/-- The sections of `h_W` over an open of `X` form a subsingleton. -/
instance subsingleton_opensRepr_obj (W : S.X.Opens) (V : (S.X.Opens)ᵒᵖ) :
    Subsingleton ((opensRepr W).obj V) :=
  inferInstanceAs (Subsingleton (ULift (V.unop ⟶ W)))

/-- A section of `h_W` over an open `V` of `X` is the same thing as the inclusion `V ≤ W`. -/
theorem nonempty_opensRepr_obj_iff (W V : S.X.Opens) :
    Nonempty ((opensRepr W).obj (op V)) ↔ V ≤ W :=
  ⟨fun ⟨t⟩ ↦ leOfHom t.down, fun h ↦ ⟨ULift.up (homOfLE h)⟩⟩

/-- **`h_W` is a sheaf.**  Its values are subsingletons, so the content is that an open `V` all of
whose points have a neighbourhood in `V` contained in `W` is itself contained in `W`. -/
theorem isSheaf_opensRepr (W : S.X.Opens) :
    Presheaf.IsSheaf (Opens.grothendieckTopology S.X.carrier) (opensRepr W) := by
  rw [isSheaf_iff_isSheaf_of_type]
  intro V T hT
  refine isSheafFor_of_subsingleton (fun _ ↦ inferInstance) _ fun x ↦ ?_
  rw [nonempty_opensRepr_obj_iff]
  intro p hp
  obtain ⟨V', f, hf, hp'⟩ := (Opens.mem_grothendieckTopology _).1 hT p hp
  exact leOfHom (x f hf).down hp'

/-- **The sheaf on `X_Zar` represented by an open `W` of `X`.** -/
def opensReprSheaf (W : S.X.Opens) :
    Sheaf (Opens.grothendieckTopology S.X.carrier) (Type (u + 1)) :=
  ⟨opensRepr W, isSheaf_opensRepr W⟩

section CoverRefinement

/-- **The images in `X_Zar` of the pullback of a Zariski covering sieve cover.**  Let
`{Aᵢ ⟶ A}` be a Zariski covering family of `Cris(X/S)` and `p : B ⟶ A`.  The restrictions of `B`
to the preimages in its ambient scheme of the ambient opens of the `Aᵢ` form a Zariski covering
family of `B` each of whose members factors through some `Aᵢ` after `p`, so it refines the
pullback of the sieve generated by `{Aᵢ ⟶ A}`; the images of a Zariski covering family cover by
[Stacks, Tag 07IL].

No fibre product in `Cris(X/S)` is used: the opens are pulled back on ambient schemes, by
`Crystalline.GlobalCrystallineSituation.Thickening.pullbackOpen`. -/
theorem forgetToOpens_generate_pullback_functorPushforward_mem
    {A B : CrystallineThickening S} (p : B ⟶ A) (E : PreZeroHypercover.{u + 1} A)
    (hE : CrystallineThickening.IsZariskiCovering E) :
    (((Sieve.generate E.presieve₀).pullback p).functorPushforward (forgetToOpens S)) ∈
      Opens.grothendieckTopology S.X.carrier ((forgetToOpens S).obj B) := by
  have hcart : ∀ i, Thickening.IsCartesian (E.f i).hom := hE.1
  have hE2 := hE.2
  simp only [Thickening.targetPresieve, Scheme.ofArrows_mem_precoverage_iff] at hE2
  have hsurj : ∀ y : A.obj.thickening.target.scheme,
      ∃ i, ∃ z, (E.f i).hom.targetHom.hom.base z = y := hE2.1
  have hoi : ∀ i, IsOpenImmersion (E.f i).hom.targetHom.hom := hE2.2
  set V : E.I₀ → B.obj.thickening.target.scheme.Opens := fun i ↦
    have := hoi i
    Thickening.pullbackOpen (E.f i).hom p.hom with hV
  have hcov : ∀ y : B.obj.thickening.target.scheme, ∃ i, y ∈ V i := by
    intro y
    obtain ⟨i, z, hz⟩ := hsurj (p.hom.targetHom.hom.base y)
    exact ⟨i, z, hz⟩
  have hfac : ∀ i, ((Sieve.generate E.presieve₀).pullback p).arrows
      (B.restrictOpenHom (V i)) := by
    intro i
    have := hoi i
    refine ⟨E.X i, ObjectProperty.homMk
      (Thickening.pullbackLiftHom (E.f i).hom p.hom (hcart i)), E.f i, ⟨i⟩, ?_⟩
    exact ObjectProperty.hom_ext (Thickening.IsCrystalline (S := S))
      (Thickening.pullbackLiftHom_comp (E.f i).hom p.hom (hcart i))
  refine (Opens.grothendieckTopology S.X.carrier).superset_covering
    (Sieve.functorPushforward_monotone (forgetToOpens S) B ?_)
    (forgetToOpens_zariskiCovering_functorPushforward_mem S (B.restrictOpenCover V)
      (CrystallineThickening.isZariskiCovering_restrictOpenCover B V hcov))
  rintro Z m ⟨Y, a, b, ⟨i⟩, rfl⟩
  exact ((Sieve.generate E.presieve₀).pullback p).downward_closed (hfac i) a

end CoverRefinement

/-- **The restriction of `h_W` along the forgetful functor is already a sheaf on `Cris(X/S)`.**
Its values are subsingletons, so the content is that if every member of a covering sieve of
`(U, T, δ)` has its open image in `X` inside `W`, then the open image of `U` is inside `W`.  By
`CategoryTheory.Precoverage.isSheaf_toGrothendieck_iff` this is only needed for the pullbacks of
the generating Zariski covering families, where it is
`Crystalline.GlobalCrystallineSituation.forgetToOpens_generate_pullback_functorPushforward_mem`. -/
theorem isSheaf_forgetToOpensOpCompOpensRepr (W : S.X.Opens) :
    Presheaf.IsSheaf (smallTopology S) ((forgetToOpens S).op ⋙ opensRepr W) := by
  rw [isSheaf_iff_isSheaf_of_type, Precoverage.isSheaf_toGrothendieck_iff]
  intro A B p R hR
  obtain ⟨E, rfl, hE⟩ := hR
  refine isSheafFor_of_subsingleton
    (fun X ↦ subsingleton_opensRepr_obj W ((forgetToOpens S).op.obj X)) _ fun x ↦ ?_
  change Nonempty ((opensRepr W).obj (op ((forgetToOpens S).obj B)))
  rw [nonempty_opensRepr_obj_iff]
  intro q hq
  obtain ⟨V', f, hf, hq'⟩ :=
    (Opens.mem_grothendieckTopology _).1
      (forgetToOpens_generate_pullback_functorPushforward_mem p E hE) q hq
  obtain ⟨Z, g, m, hg, -⟩ := hf
  exact le_trans (leOfHom m) (leOfHom (x g hg).down) hq'

section InverseImage

variable (W : S.X.Opens)

/-- **The inverse image `u_{X/S}^{-1}h_W` is the restriction of `h_W` along the forgetful
functor**: the sheafification in `CategoryTheory.Functor.sheafPullbackCocontinuous` is trivial
here, because that restriction is already a sheaf. -/
def zariskiInverseImageOpensReprIso :
    (zariskiToposMorphism S).inverseImage.obj (opensReprSheaf W) ≅
      (⟨(forgetToOpens S).op ⋙ opensRepr W, isSheaf_forgetToOpensOpCompOpensRepr W⟩ :
        smallTopos S) :=
  (sheafificationIso
    (⟨(forgetToOpens S).op ⋙ opensRepr W, isSheaf_forgetToOpensOpCompOpensRepr W⟩ :
      smallTopos S)).symm

/-- **The sections of `u_{X/S}^{-1}h_W` over an object of `Cris(X/S)`** are the morphisms from
the open image of that object's source to `W` in `X_Zar`, with their values lifted to the
coefficient universe. -/
def zariskiInverseImageOpensReprObjEquiv (A : CrystallineThickening S) :
    ((zariskiToposMorphism S).inverseImage.obj (opensReprSheaf W)).obj.obj (op A) ≃
      ULift.{u + 1} ((forgetToOpens S).obj A ⟶ W) :=
  ((sheafToPresheaf (smallTopology S) (Type (u + 1)) ⋙
    (evaluation _ _).obj (op A)).mapIso (zariskiInverseImageOpensReprIso W)).toEquiv

/-- The sections of `u_{X/S}^{-1}h_W` over an object of `Cris(X/S)` form a subsingleton. -/
instance subsingleton_zariskiInverseImageOpensRepr_obj (A : CrystallineThickening S) :
    Subsingleton (((zariskiToposMorphism S).inverseImage.obj
      (opensReprSheaf W)).obj.obj (op A)) :=
  (zariskiInverseImageOpensReprObjEquiv W A).subsingleton

/-- **The sections of `u_{X/S}^{-1}h_W` over an object of `Cris(X/S)`.**  There is one exactly
when the open image in `X` of the object's source lies in `W`, and there are never two: this is
the computation of [Stacks, Tag 04D3] for the cocontinuous `u_{X/S}`, in the case of a
representable sheaf on the small Zariski site. -/
theorem nonempty_zariskiInverseImage_opensRepr_iff (A : CrystallineThickening S) :
    Nonempty (((zariskiToposMorphism S).inverseImage.obj (opensReprSheaf W)).obj.obj (op A)) ↔
      (forgetToOpens S).obj A ≤ W :=
  ((zariskiInverseImageOpensReprObjEquiv W A).nonempty_congr).trans
    (nonempty_opensRepr_obj_iff (S := S) W _)

end InverseImage

section EssentialImage

variable {S' : GlobalCrystallineSituation.{u}} {f : S.S ⟶ S'.S} {g : S.X ⟶ S'.X}
  {h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber}
  [IsOpenImmersion g]

/-- **The site of elements of `u_{X/S}^{-1}h_{X'}` is the full subcategory of `Cris(X/S)` that
change of divided power base cuts out.**  An object of `Cris(X/S)` carries a section of
`u_{X/S}^{-1}h_{X'}` exactly when it is in the essential image of
`Crystalline.GlobalCrystallineSituation.smallChangeBase`: the left-hand side says that the open
image of its source lies in the open `g(X')`, and that is
`Crystalline.GlobalCrystallineSituation.smallChangeBase_essImage_iff`.

This is the category-level half of clause (d) of [Stacks, Tag 07KL], joined to the sheaf `F` whose
site of elements clause (d) is about.  It keeps the hypothesis
`Crystalline.DividedPowerScheme.IsInducedOpen` that the essential image statement carries: without
it change of base is not essentially surjective onto this subcategory, the factorization
`T ⟶ S'` of an object lying over `X'` being a morphism of divided power schemes only when the
divided power structure of `S'` is induced from that of `S`. -/
@[stacks 07KL "the sheaf F = u_{X/S}^{-1}h_{X'} of clause (d), and the identification of the \
  objects of Cris(X/S) carrying a section of it with the essential image of change of divided \
  power base.  NOT clause (d) itself, which asks that the square of smallChangeBaseZariskiSquare \
  realize the localization of morphisms of topoi of Stacks 04H1: see the module docstring of \
  ChangeBaseZariski.lean for what is still owed"]
theorem nonempty_zariskiInverseImage_opensRepr_iff_essImage
    (hf : DividedPowerScheme.IsInducedOpen f) (B : CrystallineThickening S') :
    Nonempty (((zariskiToposMorphism S').inverseImage.obj
        (opensReprSheaf g.opensRange)).obj.obj (op B)) ↔
      (smallChangeBase S S' f g h).essImage B := by
  rw [nonempty_zariskiInverseImage_opensRepr_iff, smallChangeBase_essImage_iff (h := h) hf]
  exact ⟨fun hle _ hx ↦ hle hx, fun hle _ hx ↦ hle hx⟩

end EssentialImage

end Crystalline.GlobalCrystallineSituation

end
