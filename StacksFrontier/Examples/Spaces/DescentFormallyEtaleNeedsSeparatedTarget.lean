module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlasCriterion
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Subcanonical
public import StacksFrontier.Examples.Spaces.DescentFormallyUnramifiedNeedsSeparatedRational

/-!
# Part (6) of Stacks 04CY needs a hypothesis on the target functor

The corrected part (6) of Stacks 04CY,
`AlgebraicGeometry.Space.formallyEtale_of_comp_of_isSeparated`, asks two things beyond the
source: the intermediate presheaf `G` is a sheaf for the étale topology, and the target presheaf
`H` is separated for it. The counterexample of
`AlgebraicGeometry.Space.DoubledSection.exists_not_formallyUnramified_of_comp` shows that the
condition on `G` cannot be dropped, but its `H` is representable, so it says nothing about the
condition on `H`. This file shows that the condition on `H` cannot be dropped either: part (6)
fails for a situation in which `F` and `G` are representable, hence étale sheaves, and only `H`
is not separated.

The construction moves the doubling of
`AlgebraicGeometry.Space.DoubledSection.doubled` from the middle of the situation to its end.
Given, in a big fppf site over `S`, a square-zero closed immersion `i : T ⟶ T'` of affines with
no retraction and an étale surjection `π : X ⟶ T'` with no section, take

* `F` the functor of points of `X`, `G` the functor of points of `T'`, `a = yoneda.map π`;
* `H = doubled i π`, the functor of points of `T'` with every section that factors through
  neither `X` nor `T` doubled, and `b` the transformation labelling every section false.

Then `a` is representable, surjective and étale, and `b ∘ a` is
`AlgebraicGeometry.Space.DoubledSection.fromSource`, which is formally étale: a lifting problem
for it has a target section whose restriction to the closed subobject factors through `X`, and by
formal étaleness of `π` the target section itself factors through `X`, so its label is false. But
`b` is not formally étale: the section `𝟙 T'` of `doubled` labelled true restricts over `T` to the
image of `i` under `b`, and it is not in the image of `b` at all.

The source's proof of part (6) glues local solutions of the lifting problem over an étale covering
of `T'` and then needs the glued section `w` of `G` to satisfy `b(w) = y` in `H(T')`, knowing only
that the two agree on each member of the covering. That is the step this counterexample defeats:
`b` is formally unramified, the local solutions exist and glue, and the glued section is `𝟙 T'`
labelled false, which agrees with `𝟙 T'` labelled true on the covering by `X` but not over `T'`.

## Main definitions

* `AlgebraicGeometry.Space.DoubledSection.ofTarget`: the transformation from the functor of
  points of `T'` to `doubled`, labelling every section false.
* `AlgebraicGeometry.Space.DoubledSection.situationTarget`: the counterexample as a
  representable, surjective, étale situation.

## Main results

* `AlgebraicGeometry.Space.DoubledSection.formallyEtale_fromSource`: the composite
  transformation is formally étale.
* `AlgebraicGeometry.Space.DoubledSection.not_formallyEtale_ofTarget`: the second
  transformation is not formally étale.
* `AlgebraicGeometry.Space.DoubledSection.exists_not_formallyEtale_of_isSheaf`: the general
  construction, with `F` and `G` étale sheaves and `H` not separated.
* `AlgebraicGeometry.Space.DoubledSection.Rational.not_forall_descend_formallyEtale_of_isSheaf`:
  over `Spec ℚ`, the negation of part (6) with `F` and `G` étale sheaves and `H` arbitrary.

## References

* [Stacks Project, Tag 04CY](https://stacks.math.columbia.edu/tag/04CY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

namespace DoubledSection

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {T T' X : BigFppfOver B S hS} (i : T ⟶ T') (π : X ⟶ T')

/-- The transformation from the functor of points of `T'` to `doubled`, labelling every section
false. -/
public def ofTarget : yoneda.obj T' ⟶ doubled i π where
  app V := ↾fun f : V.unop ⟶ T' => (⟨(f, False), fun h => h.elim⟩ : Doubled i π V.unop)
  naturality {V W} u := by
    refine TypeCat.homEquiv.injective (funext fun f => ?_)
    refine Subtype.ext (Prod.ext rfl ?_)
    exact propext ⟨fun h => h.elim, fun h => h.1⟩

/-- The component of `ofTarget` at `V` sends `f : V ⟶ T'` to the section `f` labelled false. -/
@[simp]
public theorem ofTarget_app {V : BigFppfOver B S hS} (f : V ⟶ T') :
    (ofTarget i π).app (op V) f = (⟨(f, False), fun h => h.elim⟩ : Doubled i π V) := rfl

/-- The composite of `yoneda.map π` with `ofTarget` is `fromSource`. -/
public theorem yoneda_map_comp_ofTarget : yoneda.map π ≫ ofTarget i π = fromSource i π := by
  ext V ξ
  rfl

/-- The transformation `fromSource` is formally étale: by formal étaleness of `π` a lifting
problem for it has a unique solution on underlying sections of `T'`, and the target section
then factors through `X`, so its label is false. -/
public theorem formallyEtale_fromSource
    (hpres : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS))
    (hπet : Etale ((BigFppfOver.toScheme B S hS).map π)) :
    FormallyEtale (fromSource i π) := by
  have hπ := formallyEtale_fromSource_comp_toTarget i π hpres hπet
  intro V₀ V hV₀ hV j hj x y hxy
  have h1 : (fromSource i π ≫ toTarget i π).app (op V₀) x =
      (yoneda.obj T').map j.op y.1.1 :=
    congrArg (fun p : Doubled i π V₀ => p.1.1) hxy
  obtain ⟨u, hu, huniq⟩ := hπ V₀ V hV₀ hV j hj x y.1.1 h1
  have hu2 : u ≫ π = y.1.1 := hu.2
  refine ⟨u, ⟨hu.1, ?_⟩, fun u' hu' => huniq u' ⟨hu'.1, ?_⟩⟩
  · refine Subtype.ext (Prod.ext hu2 ?_)
    refine propext ⟨False.elim, fun hc => y.2 hc ?_⟩
    rw [← hu2]
    exact factored_of_comp_pi i π u
  · exact congrArg (fun p : Doubled i π V => p.1.1) hu'.2

/-- The transformation `ofTarget` is formally unramified: it is injective on sections. -/
public theorem formallyUnramified_ofTarget : FormallyUnramified (ofTarget i π) := by
  intro V₀ V _ _ j _ x y _ z₁ z₂ hz₁ hz₂
  exact congrArg (fun p : Doubled i π V => p.1.1) (hz₁.2.trans hz₂.2.symm)

/-- The transformation `ofTarget` is not formally étale: the section `𝟙 T'` of `doubled`
labelled true restricts over `T` to the image of `i`, but it is not the image of any section of
the functor of points of `T'`. -/
public theorem not_formallyEtale_ofTarget
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (hT' : IsAffine ((BigFppfOver.toScheme B S hS).obj T'))
    (hi : IsSquareZeroClosedImmersion B S hS i)
    (hπ : ∀ ξ : T' ⟶ X, ξ ≫ π ≠ 𝟙 T')
    (hret : ∀ g : T' ⟶ T, g ≫ i ≠ 𝟙 T') :
    ¬ FormallyEtale (ofTarget i π) := by
  intro h
  have hid : (𝟙 T' : T' ⟶ T') ∉ Factored i π T' := by
    rintro (⟨ξ, hξ⟩ | ⟨g, hg⟩)
    · exact hπ ξ hξ
    · exact hret g hg
  have hiFact : (i ≫ 𝟙 T') ∈ Factored i π T := by
    rw [Category.comp_id]
    simpa using factored_of_comp_i i π (𝟙 T)
  have hxy : (ofTarget i π).app (op T) i =
      (doubled i π).map i.op (⟨(𝟙 T', True), fun _ => hid⟩ : Doubled i π T') := by
    refine Subtype.ext (Prod.ext (Category.comp_id i).symm ?_)
    exact propext ⟨False.elim, fun hh => absurd hiFact hh.2⟩
  obtain ⟨w, hw, -⟩ := h T T' hT hT' i hi i _ hxy
  have hFT : (False : Prop) = True := congrArg (fun p : Doubled i π T' => p.1.2) hw.2
  exact (hFT ▸ trivial : False)

variable [HasPullbacks (BigFppfOver B S hS)]

omit [HasPullbacks (BigFppfOver B S hS)] in
/-- The inverse image, along the functor to schemes, of a property of schemes which is stable
under base change is stable under base change in the site. -/
public theorem isStableUnderBaseChange_inverseImage_toScheme
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    (hpres : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS)) :
    (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange :=
  ⟨by
    intro A C C' Z a' b' a'' b'' hsq hb
    let := hpres
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := P) (hsq.map (BigFppfOver.toScheme B S hS)) hb⟩

/-- The morphism of functors of points induced by a morphism of the site whose underlying
morphism of schemes has a property stable under base change has that property relatively. -/
public theorem relative_yoneda_map
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    (hpres : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS))
    (hπ : P ((BigFppfOver.toScheme B S hS).map π)) :
    (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).relative yoneda
      (yoneda.map π) := by
  have := isStableUnderBaseChange_inverseImage_toScheme P hpres
  exact MorphismProperty.relative_map
    (P := MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)) hπ

/-- The counterexample as a representable, surjective, étale situation: the functors of points
of `X` and of `T'`, and the doubled functor of points of `T'`. -/
public def situationTarget
    (hpres : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS))
    (hπet : Etale ((BigFppfOver.toScheme B S hS).map π))
    (hπsurj : Surjective ((BigFppfOver.toScheme B S hS).map π)) :
    RepresentableSurjectiveEtaleSituation.{u} where
  B := B
  S := S
  hS := hS
  F := yoneda.obj X
  G := yoneda.obj T'
  H := doubled i π
  a := yoneda.map π
  b := ofTarget i π
  representable_a := (relative_yoneda_map π @Etale hpres hπet).1
  surjective_a := relative_yoneda_map π @Surjective hpres hπsurj
  etale_a := relative_yoneda_map π @Etale hpres hπet

/-- **Part (6) of Stacks 04CY needs a hypothesis on the target functor.** In a big fppf site
over `S` containing a square-zero closed immersion `i : T ⟶ T'` of affines with no retraction
and an étale surjection `π : X ⟶ T'` with no section, there is a representable, surjective,
étale situation whose source and intermediate presheaves are sheaves for the étale topology,
whose composite transformation is formally étale and whose second transformation is formally
unramified but not formally étale. Its target presheaf is then not separated for the étale
topology, by `AlgebraicGeometry.Space.formallyEtale_of_comp_of_isSeparated`.

So the separatedness hypothesis on the target presheaf in that corrected form of part (6)
cannot be removed, even when the intermediate presheaf is representable. -/
public theorem exists_not_formallyEtale_of_isSheaf
    (hpres : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS))
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (hT' : IsAffine ((BigFppfOver.toScheme B S hS).obj T'))
    (hi : IsSquareZeroClosedImmersion B S hS i)
    (hπet : Etale ((BigFppfOver.toScheme B S hS).map π))
    (hπsurj : Surjective ((BigFppfOver.toScheme B S hS).map π))
    (hπ : ∀ ξ : T' ⟶ X, ξ ≫ π ≠ 𝟙 T')
    (hret : ∀ g : T' ⟶ T, g ≫ i ≠ 𝟙 T') :
    ∃ s : RepresentableSurjectiveEtaleSituation.{u},
      s.B = B ∧ s.S = S ∧
        Presheaf.IsSheaf ((etaleTopology s.B).over (s.B.obj s.hS)) s.F ∧
        Presheaf.IsSheaf ((etaleTopology s.B).over (s.B.obj s.hS)) s.G ∧
        ¬ Presieve.IsSeparated ((etaleTopology s.B).over (s.B.obj s.hS)) s.H ∧
        FormallyEtale (s.a ≫ s.b) ∧ FormallyUnramified s.b ∧ ¬ FormallyEtale s.b := by
  have hsheaf (Y : BigFppfOver B S hS) :
      Presheaf.IsSheaf ((etaleTopology B).over (B.obj hS)) (yoneda.obj Y) :=
    isSheaf_etaleTopologyOver_of_isSheaf B S hS (BigFppfOver.isSheaf_yoneda_obj B S hS Y)
  have hG := hsheaf T'
  have hba : FormallyEtale (yoneda.map π ≫ ofTarget i π) := by
    rw [yoneda_map_comp_ofTarget]
    exact formallyEtale_fromSource i π hpres hπet
  have hne := not_formallyEtale_ofTarget i π hT hT' hi hπ hret
  refine ⟨situationTarget i π hpres hπet hπsurj, rfl, rfl,
    hsheaf X, hG, fun hH => hne ?_, hba, formallyUnramified_ofTarget i π, hne⟩
  exact formallyEtale_of_comp_of_isSeparated (situationTarget i π hpres hπet hπsurj) hG hH hba

end DoubledSection

namespace DoubledSection.Rational

/-- **A representable, surjective, étale situation over `Spec ℚ` in which part (6) of Stacks
04CY fails although the source and intermediate presheaves are étale sheaves.** Its composite
transformation is formally étale and its second transformation is formally unramified but not
formally étale; its target presheaf is not separated for the étale topology. -/
public theorem exists_not_formallyEtale_of_isSheaf :
    ∃ s : RepresentableSurjectiveEtaleSituation.{0},
      Presheaf.IsSheaf ((etaleTopology s.B).over (s.B.obj s.hS)) s.F ∧
        Presheaf.IsSheaf ((etaleTopology s.B).over (s.B.obj s.hS)) s.G ∧
        ¬ Presieve.IsSeparated ((etaleTopology s.B).over (s.B.obj s.hS)) s.H ∧
        FormallyEtale (s.a ≫ s.b) ∧ FormallyUnramified s.b ∧ ¬ FormallyEtale s.b := by
  obtain ⟨s, -, -, hF, hG, hH, het, hnu, hne⟩ := DoubledSection.exists_not_formallyEtale_of_isSheaf
    i π (preservesLimitsOfShape_walkingCospan_toScheme site S site_contains_Q)
    (inferInstanceAs (IsAffine (Spec (CommRingCat.of ℚ))))
    (inferInstanceAs (IsAffine (Spec (CommRingCat.of D))))
    isFirstOrderThickening_fstC etale_piC surjective_piC
    (fun ξ _ => not_hom_spec ((BigFppfOver.toScheme site S site_contains_Q).map ξ))
    (fun g hg => not_retraction_spec ((BigFppfOver.toScheme site S site_contains_Q).map g)
      (by
        have h := congrArg (BigFppfOver.toScheme site S site_contains_Q).map hg
        rwa [Functor.map_comp, CategoryTheory.Functor.map_id] at h))
  exact ⟨s, hF, hG, hH, het, hnu, hne⟩

/-- **Part (6) of Stacks 04CY is false when only the intermediate functor is asked to be an
étale sheaf.** The universal statement "for every representable, surjective, étale `a : F ⟶ G`
and every `b : G ⟶ H` with `F` and `G` étale sheaves, `b` is formally étale when `b ∘ a` is"
fails, already over `Spec ℚ`.

So the corrected part (6), `AlgebraicGeometry.Space.formallyEtale_of_comp_of_isSeparated`, needs
its hypothesis on the target functor `H` as well as its hypothesis on `G`; the latter is shown
necessary by `AlgebraicGeometry.Space.DoubledSection.Rational.not_forall_descend`. -/
@[stacks 04CY "counterexample to part (6) with G an étale sheaf and H arbitrary: the condition \
on H in the corrected form cannot be dropped"]
public theorem not_forall_descend_formallyEtale_of_isSheaf :
    ¬ (∀ s : RepresentableSurjectiveEtaleSituation.{0},
        Presheaf.IsSheaf ((etaleTopology s.B).over (s.B.obj s.hS)) s.F →
        Presheaf.IsSheaf ((etaleTopology s.B).over (s.B.obj s.hS)) s.G →
        FormallyEtale (s.a ≫ s.b) → FormallyEtale s.b) := by
  obtain ⟨s, hF, hG, -, het, -, hne⟩ := exists_not_formallyEtale_of_isSheaf
  exact fun h => hne (h s hF hG het)

end DoubledSection.Rational

end AlgebraicGeometry.Space

end
