module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EnoughGeometricPoints
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleSetBaseChangeSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleStalkBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StrictHenselizationBaseChangeSections

/-!
# The base change conclusion for a flat morphism with connected strict-henselization fibres

Let

```
Y --h--> X
|e       |f
v        v
T --g--> S
```

be a cartesian square of schemes with `f` flat, and suppose that at every geometric point `x̄` of
`X` the morphism of strict henselizations `Spec(O^sh_{X,x̄}) ⟶ Spec(O^sh_{S,f(x̄)})` has
geometrically connected fibres. Then the canonical base change map `f⁻¹ g_* F ⟶ h_* e⁻¹ F` is an
isomorphism for every sheaf of sets `F` on the small étale site of `T`. This is the conclusion of
Tag 0F00.

The source's proof reads the two sides as the stalks at `x̄` of `f⁻¹ g_* F` and of `h_* e⁻¹ F`.
Tag 03Q9 identifies those stalks with the global sections of `F` over
`Spec(O^sh_{S,f(x̄)}) ×_S T` and over `Spec(O^sh_{X,x̄}) ×_X Y` respectively; the two section sets
agree by Tag 0A3H applied to the canonical morphism
`Spec(O^sh_{X,x̄}) ×_X Y ⟶ Spec(O^sh_{S,f(x̄)}) ×_S T`, which is a base change of the morphism of
strict henselizations; and the conclusion follows by Tag 03PU.

## Main definitions

* `Stacks.EtaleCohomology.StalkIsSections` — the conclusion of Tag 03Q9 for sheaves of sets, in
  the form the proof of Tag 0F00 uses.

## Main results

* `Stacks.EtaleCohomology.isIso_smallEtaleSetBaseChange_of_strictHenselizationStalks` — the
  stalkwise argument of Tag 0F00 for a sheaf `F` whose stalks satisfy the conclusion of Tag 03Q9.
  Tag 0F00 itself, with no such condition, is
  `isIso_smallEtaleSetBaseChange_of_geometricallyConnected_strictHenselization`.

## Implementation notes

Of the three inputs of the source's proof, two are discharged here and one is assumed.

The Tag 0A3H step is discharged by
`Stacks.EtaleCohomology.isIso_globalSectionsSmallEtaleInverseImage`, which inverts the *canonical*
comparison `Γ(Spec(O^sh_{S,f(x̄)}) ×_S T, F) ⟶ Γ(Spec(O^sh_{X,x̄}) ×_X Y, F)` of
`Stacks.EtaleCohomology.globalSectionsSmallEtaleInverseImage`: the morphism in question is flat
and has geometrically connected fibres because it is a base change of the morphism of strict
henselizations, by `Stacks.EtaleCohomology.isPullback_strictHenselizationPullbackMap`, and it is
quasi-compact unconditionally. The Tag 03PU step is discharged by
`Stacks.EtaleCohomology.isIso_of_geometricStalk_family`, applied to the family of geometric points
`AlgebraicGeometry.GeometricPoint.ofPoint`, whose members lie over the points of `X` and therefore
cover it.

Tag 03Q9 for sheaves of sets in degree zero is
`Stacks.EtaleCohomology.isIso_Γ_map_smallEtaleSetBaseChange_strictHenselization`, which the proof
of `isIso_smallEtaleSetBaseChange_of_geometricallyConnected_strictHenselization` uses. In this
file its conclusion is instead the explicit condition `h03Q9`, spelled out by
`Stacks.EtaleCohomology.StalkIsSections`: at each geometric point `x̄` of `X` it provides the two
stalk computations as bijections and asks that the stalk map of the base change map agree,
through them, with the canonical comparison of global sections. Nothing else
about the two stalks is used, which is why `StalkIsSections` takes the stalk map as a variable
`ψ` instead of naming it: the map is supplied by the caller — in the theorem below, by the stalk
map itself — and the definition says of it only what Tag 03Q9 says.

Flatness of the morphism of strict henselizations, which Tag 0A3H needs and the source leaves
implicit in the flatness of `f`, is carried as the hypothesis `hflat`; it follows from `Flat f` by
`AlgebraicGeometry.flat_strictHenselizationSquareMap`, so assuming it rather than `Flat f` is a
generalization. The quasi-compactness and quasi-separatedness of `g` that the source assumes are
needed only for Tag 03Q9 and are therefore absent from the statements below, which are
correspondingly more general.

## References

* [Stacks Project, Tag 0F00](https://stacks.math.columbia.edu/tag/0F00)
* [Stacks Project, Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9)
* [Stacks Project, Tag 03PU](https://stacks.math.columbia.edu/tag/03PU)
* [Stacks Project, Tag 0A3H](https://stacks.math.columbia.edu/tag/0A3H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe w u v

namespace Stacks.EtaleCohomology

/-- A map of types is an isomorphism as soon as it agrees, through bijections on its source and
on its target, with an isomorphism. This is the only use made of the two stalk computations that
Tag 03Q9 supplies. -/
private theorem isIso_of_equiv_comm {A B C D : Type w} (φ : A ⟶ B) (θ : C ⟶ D) (α : A ≃ C)
    (β : B ≃ D) (hθ : IsIso θ) (hcomm : ∀ a, β (φ a) = θ (α a)) : IsIso φ := by
  have hbij : Function.Bijective θ := (isIso_iff_bijective θ).1 hθ
  refine (isIso_iff_bijective φ).2 ⟨fun a b hab ↦ α.injective (hbij.1 ?_), fun t ↦ ?_⟩
  · rw [← hcomm a, ← hcomm b, hab]
  · obtain ⟨c, hc⟩ := hbij.2 (β t)
    refine ⟨α.symm c, β.injective ?_⟩
    rw [hcomm, Equiv.apply_symm_apply]
    exact hc

section Conclusion

variable (B : BigEtaleSite.{u}) {X S Y T : Scheme.{u}} (hX : B.Contains X) (hS : B.Contains S)
  (f : X ⟶ S) {h : Y ⟶ X} {e : Y ⟶ T} {g : T ⟶ S}

/-- The inverse image of a sheaf of sets `F` on `T` along the projection
`Spec(O^sh_{S,f(x̄)}) ×_S T ⟶ T`. Tag 03Q9 identifies its global sections with the stalk of
`g_* F` at `f(x̄)`, hence with the stalk of `f⁻¹ g_* F` at `x̄`. -/
@[sga "4½ Arcata 2.3.3"]
abbrev strictHenselizationBasePullbackSheaf (x : GeometricPoint X)
    (F : Sheaf (smallEtaleTopology T) (Type (max (u + 1) v))) :
    Sheaf (smallEtaleTopology (strictHenselizationPullback B hS (x.map f) g))
      (Type (max (u + 1) v)) :=
  (smallEtaleInverseImage.{u, v}
    (pullback.snd (strictHenselizationToBase B S hS (x.map f)) g)).obj F

/-- **The conclusion of Tag 03Q9 for sheaves of sets**, in the form in which the proof of Tag
0F00 uses it. The map `ψ` is the stalk at a geometric point `x̄` of `X` of the canonical base
change map `f⁻¹ g_* F ⟶ h_* e⁻¹ F`; the condition says that the stalk of `f⁻¹ g_* F` at `x̄` is
the set of global sections of `F` over `Spec(O^sh_{S,f(x̄)}) ×_S T`, that the stalk of
`h_* e⁻¹ F` at `x̄` is the set of global sections over `Spec(O^sh_{X,x̄}) ×_X Y`, and that `ψ` is,
through those two identifications, the canonical comparison of global sections along
`Spec(O^sh_{X,x̄}) ×_X Y ⟶ Spec(O^sh_{S,f(x̄)}) ×_S T`.

The stalk map is left as the variable `ψ`, supplied by the caller, because that is all the proof
of Tag 0F00 needs of it; see this file's implementation notes. -/
def StalkIsSections (sq : IsPullback h e f g)
    (F : Sheaf (smallEtaleTopology T) (Type (max (u + 1) v))) (x : GeometricPoint X)
    {A B' : Type (max (u + 1) v)} (ψ : A ⟶ B') : Prop :=
  ∃ (α : A ≃ (Sheaf.Γ (smallEtaleTopology (strictHenselizationPullback B hS (x.map f) g))
        (Type (max (u + 1) v))).obj (strictHenselizationBasePullbackSheaf B hS f x F))
      (β : B' ≃ (smallEtaleInverseImage.{u, v} (strictHenselizationPullbackMap B hX hS f x sq) ⋙
        Sheaf.Γ (smallEtaleTopology (strictHenselizationPullback B hX x h))
          (Type (max (u + 1) v))).obj (strictHenselizationBasePullbackSheaf B hS f x F)),
    ∀ t, β (ψ t) =
      (globalSectionsSmallEtaleInverseImage.{u, v}
        (strictHenselizationPullbackMap B hX hS f x sq)).app
        (strictHenselizationBasePullbackSheaf B hS f x F) (α t)

/-- A map which the conclusion of Tag 03Q9 presents as the stalk at a geometric point `x̄` of `X`
of the base change map is an isomorphism: it is then the canonical comparison of global sections
along `Spec(O^sh_{X,x̄}) ×_X Y ⟶ Spec(O^sh_{S,f(x̄)}) ×_S T`, and that morphism is flat,
quasi-compact and has geometrically connected fibres, being a base change of the morphism of
strict henselizations, so Tag 0A3H — in the form of Tag 0EZK — applies to it. -/
private theorem isIso_of_stalkIsSections (sq : IsPullback h e f g)
    (F : Sheaf (smallEtaleTopology T) (Type (max (u + 1) v))) (x : GeometricPoint X)
    (hflat : Flat (strictHenselizationSquareMap B hX hS f x))
    (hconn : GeometricallyConnected (strictHenselizationSquareMap B hX hS f x))
    {A B' : Type (max (u + 1) v)} (ψ : A ⟶ B')
    (hstalk : StalkIsSections.{u, v} B hX hS f sq F x ψ) : IsIso ψ := by
  obtain ⟨α, β, hcompat⟩ := hstalk
  have hpb := isPullback_strictHenselizationPullbackMap B hX hS f x sq
  have : Flat (strictHenselizationPullbackMap B hX hS f x sq) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb hflat
  have : GeometricallyConnected (strictHenselizationPullbackMap B hX hS f x sq) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb hconn
  have : IsIso (globalSectionsSmallEtaleInverseImage.{u, v}
      (strictHenselizationPullbackMap B hX hS f x sq)) :=
    isIso_globalSectionsSmallEtaleInverseImage.{u, v}
      (strictHenselizationPullbackMap B hX hS f x sq)
      (universally_isQuotientMap_of_flat_quasiCompact _)
  have hcomparison : IsIso ((globalSectionsSmallEtaleInverseImage.{u, v}
      (strictHenselizationPullbackMap B hX hS f x sq)).app
      (strictHenselizationBasePullbackSheaf B hS f x F)) := inferInstance
  exact isIso_of_equiv_comm.{max (u + 1) v} ψ
    ((globalSectionsSmallEtaleInverseImage.{u, v}
      (strictHenselizationPullbackMap B hX hS f x sq)).app
      (strictHenselizationBasePullbackSheaf B hS f x F))
    α β hcomparison hcompat

/-- **The stalkwise argument of Tag 0F00.** Let

```
Y --h--> X
|e       |f
v        v
T --g--> S
```

be a cartesian square of schemes and suppose that at every geometric point `x̄` of `X` the
morphism of strict henselizations `Spec(O^sh_{X,x̄}) ⟶ Spec(O^sh_{S,f(x̄)})` is flat with
geometrically connected fibres. Then the canonical base change map `f⁻¹ g_* F ⟶ h_* e⁻¹ F` is an
isomorphism for every sheaf of sets `F` on the small étale site of `T`.

The hypothesis `h03Q9` is the conclusion of Tag 03Q9 for sheaves of sets, as recorded by
`Stacks.EtaleCohomology.StalkIsSections`; see this file's implementation notes. -/
theorem isIso_smallEtaleSetBaseChange_of_strictHenselizationStalks (sq : IsPullback h e f g)
    (F : Sheaf (smallEtaleTopology T) (Type (max (u + 1) v)))
    (hflat : ∀ x : GeometricPoint X, Flat (strictHenselizationSquareMap B hX hS f x))
    (hconn : ∀ x : GeometricPoint X,
      GeometricallyConnected (strictHenselizationSquareMap B hX hS f x))
    (h03Q9 : ∀ x : GeometricPoint X, StalkIsSections.{u, v} B hX hS f sq F x
      ((pointSmallEtale x.hom).sheafFiber.map
        ((smallEtaleSetBaseChange.{u, v} e h g f sq.w.symm).app F))) :
    IsIso ((smallEtaleSetBaseChange.{u, v} e h g f sq.w.symm).app F) := by
  refine isIso_of_geometricStalk_family (fun z : X ↦ (GeometricPoint.ofPoint X z).hom) ?_ _
    fun z ↦ ?_
  · refine Set.eq_univ_iff_forall.mpr fun z ↦ Set.mem_iUnion.mpr ⟨z, default, ?_⟩
    exact GeometricPoint.ofPoint_liesOver X z
  · exact isIso_of_stalkIsSections B hX hS f sq F (GeometricPoint.ofPoint X z) (hflat _)
      (hconn _) _ (h03Q9 _)

end Conclusion

end Stacks.EtaleCohomology

end
