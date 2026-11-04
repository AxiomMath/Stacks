module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeStackDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.VaryingBase.FiniteTypeEffective
public import StacksFrontier.AlgebraicGeometry.Quot.StackOfSpaces
public import StacksFrontier.AlgebraicGeometry.Quot.StackOfSpacesGroupoid
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFpqcLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.FinitePresentationFpqcLocality
public import StacksFrontier.CategoryTheory.Sites.Stack.GroupoidOfStack
public import StacksFrontier.CategoryTheory.Sites.Stack.StackBridge.ReverseEffective
import StacksCore.Tactic.StacksAttribute

/-!
# The stacks of families of algebraic spaces (Stacks 0D1G)

`Spaces'_ft` is the category of algebraic spaces of finite type over varying schemes of the big
fppf site of `S`, with cartesian squares as morphisms
(`AlgebraicGeometry.CartesianFiniteTypeSpaces`, Stacks 0D1E), and `Spaces'_{fp, flat, proper}` its
full subcategory of finitely presented, flat and proper families
(`AlgebraicGeometry.CartesianProperFlatSpaces`, Stacks 0D1D). Stacks 0D1G says that both are stacks
in groupoids over the big fppf site.

`Spaces'_ft` is the category fibred in groupoids attached to the stack of finite-type algebraic
spaces of Stacks 04UD (`AlgebraicGeometry.finiteTypeSpacesProjection_isStack_of_bootstrap`), which
is a stack in groupoids by Stacks 03YI; the strongly cartesian morphisms of the finite-type
families are the cartesian squares (`CategoryTheory.Functor.stronglyCartesianOver_restrict`). For
the finitely presented, flat and proper families, Stacks 04TU applied inside the finite-type
families gives a stack, since the three properties are stable under base change (Stacks 03XR, 03MO,
04WP) and local on the base for the fppf topology (Stacks 041V, 041W, 0422), and the rest is the
same.

## Main results

* `AlgebraicGeometry.stackOfSpaces_isStackInGroupoids`: **Stacks 0D1G**, both assertions.
* `AlgebraicGeometry.cartesianFiniteTypeProjection_isStackInGroupoids` and
  `AlgebraicGeometry.cartesianProperFlatProjection_isStackInGroupoids`: the two assertions, in the
  sense of Stacks 02ZI.
* `AlgebraicGeometry.cartesianFiniteTypeProjection_isStack` and
  `AlgebraicGeometry.cartesianProperFlatProjection_isStack`: the two assertions in the form of
  Stacks 02ZJ (3), fibred in groupoids and a stack in the sense of Stacks 026F.
* `AlgebraicGeometry.properFlatSpacesProjection_isStack`: the finitely presented, flat and proper
  families with all morphisms form a stack.

## References

* [Stacks Project, Tag 0D1G](https://stacks.math.columbia.edu/tag/0D1G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

universe v₁ v₂ u₁ u₂

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : Type u₂} [Category.{v₂} 𝒳]

/-- For a full subcategory closed under strongly cartesian pullback, a morphism is strongly
cartesian over the restricted functor exactly when it is strongly cartesian over the ambient one.
So the category fibred in groupoids of Stacks 03WQ attached to the restriction is the wide
subcategory of the restriction on the morphisms strongly cartesian in the ambient category. -/
theorem stronglyCartesianOver_restrict (p : 𝒳 ⥤ 𝒮) (P : ObjectProperty 𝒳) [p.IsFibered]
    (hP : ClosedUnderStronglyCartesian p P) :
    stronglyCartesianOver (restrict p P) = (stronglyCartesianOver p).inverseImage P.ι := by
  ext a b φ
  constructor
  · intro h
    have h' : (restrict p P).IsStronglyCartesian ((restrict p P).map φ) φ := h
    have hc : p.IsCartesian ((restrict p P).map φ) (P.ι.map φ) :=
      isCartesian_map_ι p P hP _ φ inferInstance
    exact (inferInstance : p.IsStronglyCartesian ((restrict p P).map φ) (P.ι.map φ))
  · intro h
    exact isStronglyCartesian_of_isStronglyCartesian_map_ι p P _ φ h

end CategoryTheory.Functor

namespace AlgebraicGeometry

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The category fibred in groupoids attached to the stack of finite-type algebraic spaces is the
category of finite-type algebraic spaces with cartesian squares as morphisms. -/
theorem stronglyCartesianOver_finiteTypeSpacesProjection :
    stronglyCartesianOver (finiteTypeSpacesProjection B S hS) =
      (stronglyCartesianOver (spacesProjection B S hS)).inverseImage
        (isFiniteTypeSpace B S hS).ι :=
  have := spacesProjection_isFibered B S hS
  Functor.stronglyCartesianOver_restrict _ _ (closedUnderStronglyCartesian_isFiniteTypeSpace B S hS)

add_to_stacks 0D1G "Spaces'_ft is a stack in groupoids (Stacks 02ZI)"
  AlgebraicGeometry.cartesianFiniteTypeProjection_isStackInGroupoids

/-- A stack in groupoids at the index universe of the base, fibred in groupoids, is a stack in the
sense of Stacks 026F, so the two assertions of Stacks 02ZJ (3) hold. -/
private theorem isFiberedInGroupoids_and_isStack_of_isStackInGroupoids.{a, b, c, d}
    {𝒞 : Type a} [Category.{b} 𝒞] [HasPullbacks 𝒞] {𝒳 : Type c} [Category.{d} 𝒳] (p : 𝒳 ⥤ 𝒞)
    (J : GrothendieckTopology 𝒞) (h : p.IsFiberedInGroupoids)
    (hs : p.IsStackInGroupoids.{max a b} J) :
    p.IsFiberedInGroupoids ∧ p.IsStack J := by
  have : p.IsFibered := h.isFibered
  exact ⟨h, Functor.isStack_of_isStackInGroupoids hs⟩

/-- **Stacks 0D1G**, the finite-type families, in the form of Stacks 02ZJ (3): `Spaces'_ft` is
fibred in groupoids and is a stack over the big fppf site of `S` (Stacks 026F). -/
@[stacks 0D1G "Spaces'_ft is fibred in groupoids and a stack (Stacks 02ZJ (3))"]
theorem cartesianFiniteTypeProjection_isStack :
    (cartesianFiniteTypeProjection B S hS).IsFiberedInGroupoids ∧
      (cartesianFiniteTypeProjection B S hS).IsStack (BigFppfOver.topology B S hS) := by
  exact isFiberedInGroupoids_and_isStack_of_isStackInGroupoids _ _
    (cartesianFiniteTypeProjection_isFiberedInGroupoids B S hS)
    (cartesianFiniteTypeProjection_isStackInGroupoids B S hS)

namespace FiniteTypeSpacesDescent

attribute [local instance] finiteTypeSpacesProjection_isFibered

variable {B S hS}

/-- A property of morphisms of algebraic spaces respecting isomorphisms holds for the structure
morphism of an algebraic space over a scheme as soon as it holds for that of an isomorphic one. -/
theorem prop_hom_of_iso (Pr : MorphismProperty (AlgebraicSpaces B S hS)) [Pr.RespectsIso]
    {A C : Comma (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F)) (yoneda : BigFppfOver B S hS ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)}
    (e : A ≅ C)
    (h : Pr (ObjectProperty.homMk C.hom :
      C.left ⟶ schemeSpace C.right)) :
    Pr (ObjectProperty.homMk A.hom :
      A.left ⟶ schemeSpace A.right) := by
  let eR : (⟨yoneda.obj A.right, isAlgebraicSpace_yoneda B S hS A.right⟩ : AlgebraicSpaces B S hS) ≅
      ⟨yoneda.obj C.right, isAlgebraicSpace_yoneda B S hS C.right⟩ :=
    (ObjectProperty.fullyFaithfulι _).preimageIso (yoneda.mapIso ((Comma.snd _ _).mapIso e))
  refine (Pr.arrow_mk_iso_iff (Arrow.isoMk ((Comma.fst _ _).mapIso e) eR ?_)).2 h
  apply ObjectProperty.hom_ext
  exact e.hom.w

/-- The structure morphism of an object of a fibre, read through the identification of its base
with `V`, has a property respecting isomorphisms exactly when the structure morphism itself has
it. -/
theorem prop_fibreStructure_iff (Pr : MorphismProperty (AlgebraicSpaces B S hS)) [Pr.RespectsIso]
    {V : BigFppfOver B S hS} (x : (finiteTypeSpacesProjection B S hS).Fiber V) :
    Pr (ObjectProperty.homMk (fibreStructure x) :
        x.1.obj.left ⟶ schemeSpace V) ↔
      Pr (ObjectProperty.homMk x.1.obj.hom :
        x.1.obj.left ⟶ schemeSpace x.1.obj.right) := by
  obtain ⟨x, rfl⟩ := x
  rw [fibreStructure_mk]

/-- **A property of morphisms of algebraic spaces local on the target for the fppf topology and
stable under base change holds for an object of a fibre of `p_ft` as soon as it holds for its
pullbacks along a covering family.** -/
theorem prop_of_pullbackFiber (Pr : MorphismProperty (AlgebraicSpaces B S hS))
    [Pr.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u + 1} B S hS)]
    (hbc : Pr.IsStableUnderBaseChange) {U : BigFppfOver B S hS} {ι : Type (u + 1)}
    (Uᵢ : ι → BigFppfOver B S hS) (fᵢ : ∀ i, Uᵢ i ⟶ U)
    (hcov : Sieve.generate (Presieve.ofArrows Uᵢ fᵢ) ∈ BigFppfOver.topology B S hS U)
    (x : (finiteTypeSpacesProjection B S hS).Fiber U)
    (hx : ∀ i, Pr (ObjectProperty.homMk (fibreStructure (Functor.pullbackFiber _ x (fᵢ i))) :
      _ ⟶ schemeSpace (Uᵢ i))) :
    Pr (ObjectProperty.homMk (fibreStructure x) :
      x.1.obj.left ⟶ schemeSpace U) := by
  classical
  let R := Sieve.generate (Presieve.ofArrows Uᵢ fᵢ)
  let K := {g : Functor.SieveDescentDatum.ArrowIndex R //
    Flat ((BigFppfOver.toScheme B S hS).map (Functor.SieveDescentDatum.arrowHom R g)) ∧
    LocallyOfFinitePresentation
      ((BigFppfOver.toScheme B S hS).map (Functor.SieveDescentDatum.arrowHom R g))}
  have hsurj : ∀ y : (BigFppfOver.toScheme B S hS).obj U, ∃ (k : K)
      (z : (BigFppfOver.toScheme B S hS).obj (Functor.SieveDescentDatum.arrowSrc R k.1)),
        (BigFppfOver.toScheme B S hS).map (Functor.SieveDescentDatum.arrowHom R k.1) z = y := by
    intro y
    obtain ⟨c, q, hq, hfl, hlfp, z, hz⟩ := BigFppfOver.exists_mem_of_mem_topology B S hS hcov y
    exact ⟨⟨R.arrows.categoryMk q hq, hfl, hlfp⟩, z, hz⟩
  have hcovK := Space.ofArrows_yoneda_mem_fppfPrecoverage.{u, u + 1} B S hS
    (fun k : K ↦ Functor.SieveDescentDatum.arrowSrc R k.1)
    (fun k ↦ Functor.SieveDescentDatum.arrowHom R k.1) (fun k ↦ k.2.1) (fun k ↦ k.2.2) hsurj
  refine (MorphismProperty.IsLocalAtTarget.iff_of_forall_pullbackSnd (P := Pr)
    (K := Space.Topology.fppf.precoverage.{u, u + 1} B S hS) hcovK).2 ?_
  intro T q _ hq
  obtain ⟨k⟩ := hq
  obtain ⟨Y, h, f', hf', hcomp⟩ := k.1.property
  obtain ⟨i⟩ := hf'
  let E₁ := Functor.pullbackFiber _ x (fᵢ i)
  let E₂ := Functor.pullbackFiber _ E₁ h
  have sq := (isPullback_pullbackMap E₁ h).paste_horiz (isPullback_pullbackMap x (fᵢ i))
  rw [← yoneda.map_comp, hcomp] at sq
  have hsqA : IsPullback
      (ObjectProperty.homMk ((toPresheaf B S hS).map (Functor.IsPreFibered.pullbackMap E₁.2 h) ≫
        (toPresheaf B S hS).map (Functor.IsPreFibered.pullbackMap x.2 (fᵢ i))) :
        E₂.1.obj.left ⟶ x.1.obj.left)
      (ObjectProperty.homMk (fibreStructure E₂) :
        _ ⟶ ⟨yoneda.obj (Functor.SieveDescentDatum.arrowSrc R k.1),
          isAlgebraicSpace_yoneda B S hS _⟩)
      (ObjectProperty.homMk (fibreStructure x) :
        x.1.obj.left ⟶ ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
      (ObjectProperty.homMk (yoneda.map (Functor.SieveDescentDatum.arrowHom R k.1)) :
        (⟨yoneda.obj (Functor.SieveDescentDatum.arrowSrc R k.1),
            isAlgebraicSpace_yoneda B S hS _⟩ : AlgebraicSpaces B S hS) ⟶ _) :=
    IsPullback.of_map_of_faithful (ObjectProperty.ι _) sq
  have hsq₂ : IsPullback
      (ObjectProperty.homMk ((toPresheaf B S hS).map (Functor.IsPreFibered.pullbackMap E₁.2 h)) :
        E₂.1.obj.left ⟶ E₁.1.obj.left)
      (ObjectProperty.homMk (fibreStructure E₂) :
        _ ⟶ ⟨yoneda.obj (Functor.SieveDescentDatum.arrowSrc R k.1),
          isAlgebraicSpace_yoneda B S hS _⟩)
      (ObjectProperty.homMk (fibreStructure E₁) :
        _ ⟶ ⟨yoneda.obj (Uᵢ i), isAlgebraicSpace_yoneda B S hS _⟩)
      (ObjectProperty.homMk (yoneda.map h)) :=
    IsPullback.of_map_of_faithful (ObjectProperty.ι _) (isPullback_pullbackMap E₁ h)
  have hE₂ := hbc.of_isPullback hsq₂ (hx i)
  rw [← hsqA.isoPullback_hom_snd] at hE₂
  exact (Pr.cancel_left_of_respectsIso hsqA.isoPullback.hom _).mp hE₂

end FiniteTypeSpacesDescent

open FiniteTypeSpacesDescent

attribute [local instance] finiteTypeSpacesProjection_isFibered

/-- A finite-type family of algebraic spaces whose structure morphism is moreover of finite
presentation, flat and proper. -/
abbrev isProperFlatFiniteTypeSpace : ObjectProperty (FiniteTypeSpaces B S hS) :=
  fun X ↦ isProperFlatSpace B S hS X.obj

/-- Condition (1) of Stacks 04TU for the finitely presented, flat and proper families inside the
finite-type ones: they are closed under strongly cartesian pullback. -/
theorem closedUnderStronglyCartesian_isProperFlatFiniteTypeSpace :
    Functor.ClosedUnderStronglyCartesian (finiteTypeSpacesProjection B S hS)
      (isProperFlatFiniteTypeSpace B S hS) := by
  have := spacesProjection_isFibered B S hS
  intro V U y x f φ hφ hx
  refine Functor.isoOverId_of_prop ?_
  have hc : (spacesProjection B S hS).IsCartesian f ((isFiniteTypeSpace B S hS).ι.map φ) :=
    Functor.isCartesian_map_ι _ _ (closedUnderStronglyCartesian_isFiniteTypeSpace B S hS) f φ
      inferInstance
  have hs : (spacesProjection B S hS).IsStronglyCartesian f
      ((isFiniteTypeSpace B S hS).ι.map φ) :=
    Functor.IsFibered.isStronglyCartesian_of_isCartesian _ f _
  obtain ⟨y', hy', e, -⟩ := closedUnderStronglyCartesian_isProperFlatSpace B S hS f
    ((isFiniteTypeSpace B S hS).ι.map φ) hs hx
  exact ⟨@prop_hom_of_iso _ _ _ _
      (@MorphismProperty.IsStableUnderBaseChange.respectsIso _ _ _
        (Space.isFinitePresentation_isStableUnderBaseChange B S hS)) _ _ e hy'.1,
    @prop_hom_of_iso _ _ _ _
      (@MorphismProperty.IsStableUnderBaseChange.respectsIso _ _ _
        (Space.isFlat_isStableUnderBaseChange B S hS)) _ _ e hy'.2.1,
    @prop_hom_of_iso _ _ _ _
      (@MorphismProperty.IsStableUnderBaseChange.respectsIso _ _ _
        (Space.isProper_isStableUnderBaseChange B S hS)) _ _ e hy'.2.2⟩

/-- Condition (3) of Stacks 04TU for the finitely presented, flat and proper families inside the
finite-type ones: being of finite presentation, flat and proper is local on the base for the fppf
topology (Stacks 041V, 041W and 0422). -/
theorem locallyClosed_isProperFlatFiniteTypeSpace :
    Functor.LocallyClosed (finiteTypeSpacesProjection B S hS)
      (isProperFlatFiniteTypeSpace B S hS) (BigFppfOver.topology B S hS) := by
  intro U ι Uᵢ fᵢ hcov x hx
  refine Functor.isoOverId_of_prop ?_
  have key : ∀ (Pr : MorphismProperty (AlgebraicSpaces B S hS))
      [Pr.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u + 1} B S hS)]
      [Pr.IsStableUnderBaseChange],
      (∀ Y : FiniteTypeSpaces B S hS, isProperFlatFiniteTypeSpace B S hS Y →
        Pr (ObjectProperty.homMk Y.obj.hom :
          Y.obj.left ⟶ schemeSpace Y.obj.right)) →
      Pr (ObjectProperty.homMk x.1.obj.hom :
        x.1.obj.left ⟶ schemeSpace x.1.obj.right) := by
    intro Pr _ _ hPr
    rw [← prop_fibreStructure_iff Pr x]
    refine prop_of_pullbackFiber Pr inferInstance Uᵢ fᵢ hcov x fun i ↦ ?_
    obtain ⟨y', hy', e, -⟩ := hx i
    rw [prop_fibreStructure_iff Pr]
    exact prop_hom_of_iso Pr ((isFiniteTypeSpace B S hS).ι.mapIso e) (hPr y' hy')
  have i1 : MorphismProperty.IsLocalAtTarget
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) => Space.IsFinitePresentation B S hS f.hom)
      (Space.Topology.fppf.precoverage.{u, u + 1} B S hS) :=
    .of_le (Space.fppfPrecoverage_le_fpqcPrecoverage B S hS)
  have i2 : MorphismProperty.IsLocalAtTarget
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) => Space.IsFlat B S hS f.hom)
      (Space.Topology.fppf.precoverage.{u, u + 1} B S hS) :=
    .of_le (Space.fppfPrecoverage_le_fpqcPrecoverage B S hS)
  have i3 : (Space.properProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u + 1} B S hS) :=
    .of_le (Space.fppfPrecoverage_le_fpqcPrecoverage B S hS)
  have := Space.isFinitePresentation_isStableUnderBaseChange B S hS
  have := Space.isFlat_isStableUnderBaseChange B S hS
  have := Space.isProper_isStableUnderBaseChange B S hS
  exact ⟨key (fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) =>
      Space.IsFinitePresentation B S hS f.hom) fun _ hY ↦ hY.1,
    key (fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) => Space.IsFlat B S hS f.hom)
      fun _ hY ↦ hY.2.1,
    key (Space.properProperty B S hS) fun _ hY ↦ hY.2.2⟩

/-- The finitely presented, flat and proper families inside the finite-type ones form a stack
(Stacks 04TU). -/
theorem isProperFlatFiniteTypeSpace_isStack :
    ((isProperFlatFiniteTypeSpace B S hS).ι ⋙ finiteTypeSpacesProjection B S hS).IsStack
      (BigFppfOver.topology B S hS) :=
  Functor.IsStack.fullSubcategory _ _ (finiteTypeSpacesProjection_isStack_of_bootstrap B S hS) _
    (closedUnderStronglyCartesian_isProperFlatFiniteTypeSpace B S hS)
    (locallyClosed_isProperFlatFiniteTypeSpace B S hS)

/-- The finitely presented, flat and proper families read inside the finite-type families and
read among all families of algebraic spaces are the same category over the big fppf site. -/
def properFlatSpacesEquivalence : BasedCategory.Equivalence
    (BasedCategory.ofFunctor
      ((isProperFlatFiniteTypeSpace B S hS).ι ⋙ finiteTypeSpacesProjection B S hS))
    (BasedCategory.ofFunctor ((isProperFlatSpace B S hS).ι ⋙ spacesProjection B S hS)) where
  functor :=
    { obj X := ⟨X.obj.obj, X.property⟩
      map φ := ObjectProperty.homMk φ.hom.hom
      w := rfl }
  inverse :=
    { obj Y := ⟨⟨Y.obj, isProperFlatSpace_le_isFiniteTypeSpace B S hS _ Y.property⟩, Y.property⟩
      map φ := ObjectProperty.homMk (ObjectProperty.homMk φ.hom)
      w := rfl }
  unitIso := Iso.refl _
  counitIso := Iso.refl _

/-- The finitely presented, flat and proper families of algebraic spaces over varying schemes form
a stack over the big fppf site of `S`. -/
theorem properFlatSpacesProjection_isStack :
    ((isProperFlatSpace B S hS).ι ⋙ spacesProjection B S hS).IsStack
      (BigFppfOver.topology B S hS) :=
  (properFlatSpacesEquivalence B S hS).isStack _ (isProperFlatFiniteTypeSpace_isStack B S hS)

add_to_stacks 0D1G "Spaces'_{fp, flat, proper} is a stack in groupoids (Stacks 02ZI)"
  AlgebraicGeometry.cartesianProperFlatProjection_isStackInGroupoids

/-- **Stacks 0D1G**, the finitely presented, flat and proper families, in the form of Stacks 02ZJ
(3): `Spaces'_{fp, flat, proper}` is fibred in groupoids and is a stack over the big fppf site of
`S` (Stacks 026F). -/
@[stacks 0D1G "Spaces'_{fp, flat, proper} is fibred in groupoids and a stack (Stacks 02ZJ (3))"]
theorem cartesianProperFlatProjection_isStack :
    (cartesianProperFlatProjection B S hS).IsFiberedInGroupoids ∧
      (cartesianProperFlatProjection B S hS).IsStack (BigFppfOver.topology B S hS) := by
  exact isFiberedInGroupoids_and_isStack_of_isStackInGroupoids _ _
    (cartesianProperFlatProjection_isFiberedInGroupoids B S hS)
    (cartesianProperFlatProjection_isStackInGroupoids B S hS)

/-- **Stacks 0D1G.** The category `Spaces'_ft` is a stack in groupoids over the big fppf site of
`S`, and so is `Spaces'_{fp, flat, proper}` (Stacks 02ZI). -/
@[stacks 0D1G]
theorem stackOfSpaces_isStackInGroupoids.{w} :
    (cartesianFiniteTypeProjection B S hS).IsStackInGroupoids.{w}
        (BigFppfOver.topology B S hS) ∧
      (cartesianProperFlatProjection B S hS).IsStackInGroupoids.{w}
        (BigFppfOver.topology B S hS) :=
  ⟨cartesianFiniteTypeProjection_isStackInGroupoids B S hS,
    cartesianProperFlatProjection_isStackInGroupoids B S hS⟩

end AlgebraicGeometry

end
