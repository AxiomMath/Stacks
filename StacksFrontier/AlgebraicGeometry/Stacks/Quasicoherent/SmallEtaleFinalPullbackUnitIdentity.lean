module

public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChangeIdComp
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtaleFinalPullbackUnitComposition

/-!
# The identity law for the pullback of a section along `ε` of Stacks 070R (2)

For `a : X ⟶ Y` in a big étale site, `AlgebraicGeometry.SmallEtale.finalPullbackUnit` is the map
`Γ(Y, M) ⟶ Γ(X, ε_a^*M)` pulling a section over the final object back along `a`.
`AlgebraicGeometry.SmallEtale.finalPullbackUnit_factoredComp` proves that this rule is compatible
with composition; **this file proves that it is compatible with the identity**, which is the other
half of the functoriality of the rule `(f : T → S) ↦ Γ(T, f_small^*𝓖)` that
`PresheafOfModules` on a big site needs, and which **Stacks 070S part (3)** and clauses (1), (2),
(3), (6), (7) of **Stacks 0DEW** compare with a presheaf-level inverse image.

Stated to the lemma, what is proved is

`finalPullbackUnit B (𝟙 X) (ε_b^*𝓖) ≫ smallEtaleSectionsApp B
  ((smallEtalePullbackFactoredCompIso B (𝟙 X) b b (Category.id_comp b)).hom.app 𝓖)
  (final B X.obj X.property) = 𝟙`

for `b : X ⟶ Y` and a sheaf of modules `𝓖` on the small étale site of `Y`, together with the
cleaner statement it specialises from, `AlgebraicGeometry.SmallEtale.finalPullbackUnit_id`, in
which the comparison is the identity comparison of the pullbacks themselves and the module is an
arbitrary one on the small étale site of `X`.

## The route

A left adjoint has no formula, so the composition law for the pullbacks along `ε` is a comparison
of left adjoints given by uniqueness, and its unit law has to come from the corresponding — and
computable — law for the *pushforwards*.  That is
`CategoryTheory.Adjunction.leftAdjointCompIso_comp_id`, whose hypothesis asks for an isomorphism
`(ε_{𝟙 X})_* ≅ 𝟭` compatible with the compositor
`AlgebraicGeometry.SmallEtale.smallEtalePushforwardRightCompIso`.  So the file runs

1. `AlgebraicGeometry.SmallEtale.smallEtaleStructureMapRing_id_comp`: the structure map of
   `ε_{𝟙 X}` on sheaves of rings, read through the identification
   `AlgebraicGeometry.smallEtaleBaseChange_idIso` of the site functor with the identity, is the
   identity.  Over an étale `W / X` both maps are pullback of functions along an isomorphism and
   its inverse.
2. `AlgebraicGeometry.SmallEtale.smallEtaleModulePushforwardIdIso`: hence `(ε_{𝟙 X})_* ≅ 𝟭`,
   by `SheafOfModules.pushforwardCongr₂` followed by `SheafOfModules.pushforwardId`.  On sections
   over an object it is restriction along `AlgebraicGeometry.smallEtaleBaseChange_idIso`.
3. `AlgebraicGeometry.SmallEtale.smallEtalePushforwardRightCompIso_id_left`: the compatibility.
   On sections both sides are restriction maps, and the identity of the two arrows they restrict
   along is exactly the unit law of **Stacks 021J**,
   `AlgebraicGeometry.smallEtaleBaseChange_factoredCompIso_id_left_inv_app`.  This is the only
   step with content, and all of its content is that lemma.
4. `AlgebraicGeometry.SmallEtale.smallEtalePullbackFactoredCompIso_id_left`: Mathlib's
   `CategoryTheory.Adjunction.leftAdjointCompIso_comp_id` then transports (3) to the pullbacks,
   through `…smallEtalePullbackFactoredCompIso_eq_leftAdjointCompIso`.
5. `AlgebraicGeometry.SmallEtale.finalPullbackUnit_id`: on sections over the final object, the
   characterisation `CategoryTheory.unit_conjugateEquiv` of the comparison of a left adjoint with
   the identity turns the composite `Γ(X, M) ⟶ Γ(X, ε_{𝟙 X}^*M) ⟶ Γ(X, M)` into restriction
   along the two arrows between `final` and its base change, and those compose to the identity
   because `final` is terminal.

## Main definitions

* `AlgebraicGeometry.SmallEtale.smallEtaleModulePushforwardIdIso` and
  `AlgebraicGeometry.SmallEtale.smallEtaleModulePullbackIdIso`: the direct image and the inverse
  image along `ε_{𝟙 X}` are the identity on sheaves of modules.

## Main results

* `AlgebraicGeometry.SmallEtale.smallEtalePushforwardRightCompIso_id_left` and
  `AlgebraicGeometry.SmallEtale.smallEtalePullbackFactoredCompIso_id_left`: **the left unit law
  for the composition of the direct images, resp. the inverse images, of Stacks 070R (2).**
* `AlgebraicGeometry.SmallEtale.finalPullbackUnit_id` and
  `AlgebraicGeometry.SmallEtale.finalPullbackUnit_factoredComp_id`: **`finalPullbackUnit` at an
  identity is the identity.**

## Scope -- what is NOT proved here

Together with `AlgebraicGeometry.SmallEtale.finalPullbackUnit_factoredComp` this makes the rule
`(f : T → S) ↦ Γ(T, f_small^*𝓖)` functorial on a big site, for an arbitrary sheaf of modules
`𝓖` on `S_étale` and with no hypothesis on the morphisms.  The presheaf of modules itself is
`AlgebraicGeometry.SmallEtale.sectionsSheafTauPresheafOfModules` in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleSectionsSheafTauPresheaf.lean`,
which consumes this file's identity law as its `map_id`; it is not built here.  The comparison
of its sheafification with the inverse image along the inclusion of the small étale site, and
the local bijectivity of that comparison, are **not** here either, and no `@[stacks 070S]` or
`@[stacks 0DEW]` attribute is claimed.

## References

* [Stacks Project, Tag 021J](https://stacks.math.columbia.edu/tag/021J)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 070S](https://stacks.math.columbia.edu/tag/070S)
* [Stacks Project, Tag 0DEW](https://stacks.math.columbia.edu/tag/0DEW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (X : B.Scheme)

/-! ### Sections detect morphisms -/

/-- A morphism of sheaves of modules on a small étale site is determined by its sections over
every object: the forgetful functors to presheaves of modules and to presheaves of abelian
groups are both faithful. -/
public theorem smallEtaleSectionsApp_injective {Z : B.Scheme}
    {M N : SheafOfModules.{u} (structureSheaf B Z.obj Z.property)} {φ ψ : M ⟶ N}
    (h : ∀ W, smallEtaleSectionsApp B φ W = smallEtaleSectionsApp B ψ W) : φ = ψ :=
  (SheafOfModules.forget _).map_injective <| (PresheafOfModules.toPresheaf _).map_injective <|
    NatTrans.ext (funext fun W => h W.unop)

/-- Sections over an object take the identity to the identity. -/
@[simp]
public theorem smallEtaleSectionsApp_id {Z : B.Scheme}
    (M : SheafOfModules.{u} (structureSheaf B Z.obj Z.property))
    (W : SmallEtale B Z.obj Z.property) :
    smallEtaleSectionsApp B (𝟙 M) W = 𝟙 _ :=
  (smallEtaleSectionsFunctor B W).map_id M

/-! ### The structure map of `ε` at an identity -/

/-- The restriction maps of the small étale structure sheaf are pullback of global functions
along the underlying morphism of schemes. -/
public theorem structureSheaf_obj_map_inclusion {S : Scheme.{u}} {hS : B.Contains S}
    {W W' : SmallEtale B S hS} (k : W' ⟶ W) :
    (structureSheaf B S hS).obj.map k.op =
      (forget₂ CommRingCat.{u} RingCat.{u}).map
        (Scheme.Γ.map (op (B.inclusion.map
          ((SmallEtale.inclusion B S hS).map k).left))) := rfl

/-- The identification of base change along `𝟙 X` with the identity functor is inverse, on
underlying objects, to the projection of the fibre product with `𝟙 X`. -/
public theorem smallEtaleBaseChange_idIso_inv_left_comp_pullback_fst
    (W : SmallEtale B X.obj X.property) :
    ((SmallEtale.inclusion B X.obj X.property).map
          ((smallEtaleBaseChange_idIso B X).inv.app W)).left ≫
        Limits.pullback.fst W.obj.hom (𝟙 X) =
      𝟙 _ := by
  have h : ((SmallEtale.inclusion B X.obj X.property).map
        ((smallEtaleBaseChange_idIso B X).inv.app W)).left ≫
      ((SmallEtale.inclusion B X.obj X.property).map
        ((smallEtaleBaseChange_idIso B X).hom.app W)).left = 𝟙 _ := by
    rw [← Over.comp_left, ← Functor.map_comp, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id, Over.id_left]
  rwa [smallEtaleBaseChange_idIso_hom_app_left] at h

/-- **The structure map of `ε_{𝟙 X}` is the identity**, read through the identification
`AlgebraicGeometry.smallEtaleBaseChange_idIso` of base change along `𝟙 X` with the identity
functor.  Over an étale `W / X` the two factors are pullback of global functions along the
projection `X ×_X W ⟶ W` and along its inverse. -/
public theorem smallEtaleStructureMapRing_id_comp :
    smallEtaleStructureMapRing B (𝟙 X) ≫
        (Functor.sheafPushforwardContinuousNatTrans
          (smallEtaleBaseChange_idIso B X).symm.hom RingCat.{u}
          (topology B X.obj X.property) (topology B X.obj X.property)).app
            (structureSheaf B X.obj X.property) =
      𝟙 (structureSheaf B X.obj X.property) := by
  ext W : 3
  obtain ⟨W⟩ := W
  show (forget₂ CommRingCat.{u} RingCat.{u}).map
        (Scheme.Γ.map (op (B.inclusion.map (Limits.pullback.fst W.obj.hom (𝟙 X))))) ≫
      (forget₂ CommRingCat.{u} RingCat.{u}).map
        (Scheme.Γ.map (op (B.inclusion.map
          ((SmallEtale.inclusion B X.obj X.property).map
            ((smallEtaleBaseChange_idIso B X).inv.app W)).left))) =
    𝟙 ((forget₂ CommRingCat.{u} RingCat.{u}).obj
        (Scheme.Γ.obj (op (B.inclusion.obj W.obj.left))))
  have h1 := congrArg (fun k => (forget₂ CommRingCat.{u} RingCat.{u}).map
      (Scheme.Γ.map (op (B.inclusion.map k))))
    (smallEtaleBaseChange_idIso_inv_left_comp_pullback_fst B X W)
  simp only [CategoryTheory.Functor.map_id] at h1
  exact h1

/-! ### Direct and inverse image along `ε` at an identity -/

/-- **The direct image along `ε_{𝟙 X}` is the identity on sheaves of modules.**  The underlying
site functor is base change along `𝟙 X`, which is the identity by
`AlgebraicGeometry.smallEtaleBaseChange_idIso`, and the structure map is the identity through
that comparison by
`AlgebraicGeometry.SmallEtale.smallEtaleStructureMapRing_id_comp`. -/
public def smallEtaleModulePushforwardIdIso :
    SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B (𝟙 X)) ≅
      𝟭 (SheafOfModules.{u} (structureSheaf B X.obj X.property)) :=
  SheafOfModules.pushforwardCongr₂.{u} _ (smallEtaleBaseChange_idIso B X).symm
      (smallEtaleStructureMapRing_id_comp B X) ≪≫
    SheafOfModules.pushforwardId _

/-- On sections over an object, the identification of the direct image along `ε_{𝟙 X}` with the
identity is restriction along `AlgebraicGeometry.smallEtaleBaseChange_idIso`. -/
public theorem smallEtaleModulePushforwardIdIso_hom_sectionsApp
    (M : SheafOfModules.{u} (structureSheaf B X.obj X.property))
    (V : SmallEtale B X.obj X.property) :
    smallEtaleSectionsApp B ((smallEtaleModulePushforwardIdIso B X).hom.app M) V =
      M.val.presheaf.map ((smallEtaleBaseChange_idIso B X).inv.app V).op := rfl

/-- The inverse form of
`AlgebraicGeometry.SmallEtale.smallEtaleModulePushforwardIdIso_hom_sectionsApp`. -/
public theorem smallEtaleModulePushforwardIdIso_inv_sectionsApp
    (M : SheafOfModules.{u} (structureSheaf B X.obj X.property))
    (V : SmallEtale B X.obj X.property) :
    smallEtaleSectionsApp B ((smallEtaleModulePushforwardIdIso B X).inv.app M) V =
      M.val.presheaf.map ((smallEtaleBaseChange_idIso B X).hom.app V).op := rfl

/-- **The inverse image along `ε_{𝟙 X}` is the identity on sheaves of modules**, being the left
adjoint of a right adjoint that is. -/
public abbrev smallEtaleModulePullbackIdIso :
    SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B (𝟙 X)) ≅
      𝟭 (SheafOfModules.{u} (structureSheaf B X.obj X.property)) :=
  Adjunction.leftAdjointIdIso
    (SheafOfModules.pullbackPushforwardAdjunction.{u} (smallEtaleStructureMapRing B (𝟙 X)))
    (smallEtaleModulePushforwardIdIso B X)

/-! ### The unit law for the compositors -/

/-- **The left unit law for the compositor of the direct images of Stacks 070R (2).**  The
compositor at the factorisation `𝟙 X ≫ b = b` is the identification of the direct image along
`ε_{𝟙 X}` with the identity, whiskered.

On sections over an object `U` of the small étale site of `Y` both sides are restriction maps:
the left-hand one along the inverse comparison of **Stacks 021J** at `U`, the right-hand one
along `AlgebraicGeometry.smallEtaleBaseChange_idIso` at the base change of `U`.  That those two
arrows agree is
`AlgebraicGeometry.smallEtaleBaseChange_factoredCompIso_id_left_inv_app`, and it is the whole
content of this lemma. -/
public theorem smallEtalePushforwardRightCompIso_id_left {Y : B.Scheme} (b : X ⟶ Y) :
    smallEtalePushforwardRightCompIso B (𝟙 X) b b (Category.id_comp b) =
      Functor.isoWhiskerRight (smallEtaleModulePushforwardIdIso B X)
          (SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B b)) ≪≫
        Functor.leftUnitor _ := by
  refine Iso.ext (NatTrans.ext (funext fun M => ?_))
  refine smallEtaleSectionsApp_injective B (fun U => ?_)
  have hR : (Functor.isoWhiskerRight (smallEtaleModulePushforwardIdIso B X)
        (SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B b)) ≪≫
      Functor.leftUnitor _).hom.app M =
      (SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B b)).map
        ((smallEtaleModulePushforwardIdIso B X).hom.app M) := by simp
  rw [hR]
  refine (pushforwardRightCompIso_sectionsApp B (𝟙 X) b b (Category.id_comp b) M U).trans ?_
  refine Eq.trans ?_
    (pushforward_map_sectionsApp B b ((smallEtaleModulePushforwardIdIso B X).hom.app M) U).symm
  refine Eq.trans ?_ (smallEtaleModulePushforwardIdIso_hom_sectionsApp B X M
    ((smallEtaleBaseChange B b).obj U)).symm
  exact congrArg (fun k => M.val.presheaf.map (Quiver.Hom.op k))
    (smallEtaleBaseChange_factoredCompIso_id_left_inv_app B b U)

/-- **The left unit law for the composition of the pullbacks of Stacks 070R (2).**  This is
`AlgebraicGeometry.SmallEtale.smallEtalePushforwardRightCompIso_id_left` carried across the
adjunctions by `CategoryTheory.Adjunction.leftAdjointCompIso_comp_id`, the composition law for
the pullbacks being the comparison of left adjoints the compositor of the pushforwards
induces. -/
public theorem smallEtalePullbackFactoredCompIso_id_left {Y : B.Scheme} (b : X ⟶ Y) :
    smallEtalePullbackFactoredCompIso B (𝟙 X) b b (Category.id_comp b) =
      Functor.isoWhiskerLeft _ (smallEtaleModulePullbackIdIso B X) ≪≫
        Functor.rightUnitor _ := by
  rw [smallEtalePullbackFactoredCompIso_eq_leftAdjointCompIso]
  exact Adjunction.leftAdjointCompIso_comp_id _ _ _ _
    (smallEtalePushforwardRightCompIso_id_left B X b)

/-! ### The identity law on sections over the final object -/

/-- **The characterisation of
`AlgebraicGeometry.SmallEtale.smallEtaleModulePullbackIdIso`**: its direct image, after the unit,
is the inverse of the identification of the direct image with the identity.  This is
`CategoryTheory.unit_conjugateEquiv` at the identity adjunction, where
`CategoryTheory.Adjunction.conjugateEquiv_leftAdjointIdIso_hom` computes the conjugate. -/
public theorem unit_comp_map_smallEtaleModulePullbackIdIso
    (N : SheafOfModules.{u} (structureSheaf B X.obj X.property)) :
    (SheafOfModules.pullbackPushforwardAdjunction.{u}
          (smallEtaleStructureMapRing B (𝟙 X))).unit.app N ≫
        (SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B (𝟙 X))).map
          ((smallEtaleModulePullbackIdIso B X).hom.app N) =
      (smallEtaleModulePushforwardIdIso B X).inv.app N := by
  have h := unit_conjugateEquiv
    (Adjunction.id (C := SheafOfModules.{u} (structureSheaf B X.obj X.property)))
    (SheafOfModules.pullbackPushforwardAdjunction.{u} (smallEtaleStructureMapRing B (𝟙 X)))
    (smallEtaleModulePullbackIdIso B X).hom N
  rw [Adjunction.conjugateEquiv_leftAdjointIdIso_hom] at h
  simpa using h.symm

/-- The unit along `ε_{𝟙 X}` over the final object, followed by the sections of the
identification of the pullback with the identity over the base change of the final object, is
restriction along `AlgebraicGeometry.smallEtaleBaseChange_idIso`.

This is
`AlgebraicGeometry.SmallEtale.unit_comp_map_smallEtaleModulePullbackIdIso` read on sections, the
sections of a direct image being the sections over the base change. -/
public theorem unitSectionsApp_comp_modulePullbackIdIso
    (N : SheafOfModules.{u} (structureSheaf B X.obj X.property)) :
    unitSectionsApp B (𝟙 X) N (final B X.obj X.property) ≫
        smallEtaleSectionsApp B ((smallEtaleModulePullbackIdIso B X).hom.app N)
          ((smallEtaleBaseChange B (𝟙 X)).obj (final B X.obj X.property)) =
      N.val.presheaf.map
        ((smallEtaleBaseChange_idIso B X).hom.app (final B X.obj X.property)).op := by
  refine Eq.trans ?_
    (smallEtaleModulePushforwardIdIso_inv_sectionsApp B X N (final B X.obj X.property))
  refine Eq.trans ?_ (congrArg (fun φ => smallEtaleSectionsApp B φ (final B X.obj X.property))
    (unit_comp_map_smallEtaleModulePullbackIdIso B X N))
  exact (smallEtaleSectionsApp_comp B
    ((SheafOfModules.pullbackPushforwardAdjunction.{u}
      (smallEtaleStructureMapRing B (𝟙 X))).unit.app N)
    ((SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B (𝟙 X))).map
      ((smallEtaleModulePullbackIdIso B X).hom.app N)) (final B X.obj X.property)).symm

/-- **`AlgebraicGeometry.SmallEtale.finalPullbackUnit` at an identity is the identity.**  Pulling
a section over the final object back along `𝟙 X` and reading the result through the
identification of `ε_{𝟙 X}^*` with the identity changes nothing.

By
`AlgebraicGeometry.SmallEtale.unitSectionsApp_comp_modulePullbackIdIso` the composite is
restriction along the two arrows between the final object and its base change along `𝟙 X`, and
those compose to the identity because the final object is terminal. -/
public theorem finalPullbackUnit_id
    (N : SheafOfModules.{u} (structureSheaf B X.obj X.property)) :
    finalPullbackUnit B (𝟙 X) N ≫
        smallEtaleSectionsApp B ((smallEtaleModulePullbackIdIso B X).hom.app N)
          (final B X.obj X.property) = 𝟙 _ := by
  have hterm : (smallEtaleBaseChange_finalIsTerminal B (𝟙 X)).from (final B X.obj X.property) ≫
      (smallEtaleBaseChange_idIso B X).hom.app (final B X.obj X.property) =
      𝟙 (final B X.obj X.property) :=
    (finalIsTerminal B X.obj X.property).hom_ext _ _
  have key : N.val.presheaf.map
        ((smallEtaleBaseChange_idIso B X).hom.app (final B X.obj X.property)).op ≫
      N.val.presheaf.map
        ((smallEtaleBaseChange_finalIsTerminal B (𝟙 X)).from
          (final B X.obj X.property)).op = 𝟙 _ := by
    rw [← Functor.map_comp, ← op_comp, hterm]
    simp
  refine Eq.trans ?_ key
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun k => unitSectionsApp B (𝟙 X) N (final B X.obj X.property) ≫ k)
    (smallEtaleSectionsApp_naturality B ((smallEtaleModulePullbackIdIso B X).hom.app N)
      ((smallEtaleBaseChange_finalIsTerminal B (𝟙 X)).from (final B X.obj X.property)))) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  exact congrArg (fun k => k ≫ N.val.presheaf.map
      ((smallEtaleBaseChange_finalIsTerminal B (𝟙 X)).from (final B X.obj X.property)).op)
    (unitSectionsApp_comp_modulePullbackIdIso B X N)

/-- **The identity half of the functoriality of `(f : T → S) ↦ Γ(T, f_small^*𝓖)`.**  This is
`AlgebraicGeometry.SmallEtale.finalPullbackUnit_id` in the shape a presheaf of modules on a big
site consumes: the comparison is the composition law
`AlgebraicGeometry.SmallEtale.smallEtalePullbackFactoredCompIso` at the factorisation
`𝟙 X ≫ b = b`, and the module is the pullback of `𝓖` along `b`.

Its companion is
`AlgebraicGeometry.SmallEtale.finalPullbackUnit_factoredComp`, the composition half.  Neither
puts any hypothesis on the morphisms or on the module. -/
public theorem finalPullbackUnit_factoredComp_id {Y : B.Scheme} (b : X ⟶ Y)
    (𝓖 : SheafOfModules.{u} (structureSheaf B Y.obj Y.property)) :
    finalPullbackUnit B (𝟙 X)
          ((SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B b)).obj 𝓖) ≫
        smallEtaleSectionsApp B
          ((smallEtalePullbackFactoredCompIso B (𝟙 X) b b (Category.id_comp b)).hom.app 𝓖)
          (final B X.obj X.property) = 𝟙 _ := by
  have h : (smallEtalePullbackFactoredCompIso B (𝟙 X) b b (Category.id_comp b)).hom.app 𝓖 =
      (smallEtaleModulePullbackIdIso B X).hom.app
        ((SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B b)).obj 𝓖) := by
    rw [smallEtalePullbackFactoredCompIso_id_left]
    simp
  rw [h, finalPullbackUnit_id]

end AlgebraicGeometry.SmallEtale

end
