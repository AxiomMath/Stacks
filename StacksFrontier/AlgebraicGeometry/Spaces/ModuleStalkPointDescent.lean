module

public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricModuleStalkGerm

/-!
# Maps out of the stalk of a sheaf of modules at a point of a site

Let `F` be a sheaf of modules over a sheaf of rings `O` on a site `(C, J)` and let `p` be a
point of that site.  A compatible family of additive maps out of the sections of `F` over the
neighbourhoods of `p` determines a single additive map out of the stalk
`Stacks.moduleStalkLarge p O F`, and that map is determined by what it does to germs.  This
file constructs that descent, shows that it is semilinear along a ring map out of the fibre of
`O` when every member of the family is, and gives the variant in which the family is defined on
a presheaf of modules mapping locally bijectively to `F`.

## Main definitions

* `Stacks.moduleStalkLargeDescOfCompatibleFamily` is the additive map out of the stalk
  determined by a family of additive maps out of the sections which is compatible with
  restriction.
* `Stacks.moduleStalkLargeDescOfLocallyBijective` is the same descent for a family given on the
  sections of a presheaf of modules mapping locally bijectively to `F`.

## Main results

* `Stacks.moduleStalkLargeDescOfCompatibleFamily_germ`: the descended map sends the germ of a
  section to the value of the given family on that section.
* `Stacks.moduleStalkLarge_addHom_ext`: two additive maps out of the stalk which agree on all
  germs are equal.
* `Stacks.moduleStalkLargeDescOfCompatibleFamily_smul`: if each member of the family is
  semilinear along a fixed ring map out of the fibre of `O`, then so is the descended map.
* `Stacks.moduleStalkLargeGerm_exists_of_locallyBijective`: every element of the stalk is the
  germ of a section of a presheaf of modules mapping locally surjectively to `F`.
* `Stacks.moduleStalkLargeDescOfLocallyBijective_germ`,
  `Stacks.moduleStalkLargeDescOfLocallyBijective_smul` and
  `Stacks.moduleStalkLarge_addHom_ext_of_locallyBijective`: the same three statements for the
  descent along a locally bijective morphism.

## Implementation notes

`Stacks.moduleStalkLarge` is a colimit over a small final model of the neighbourhoods of `p`,
and `Stacks.moduleStalkLargeFinalIso` compares it with the colimit over all neighbourhoods,
which is `CategoryTheory.GrothendieckTopology.Point.presheafFiber` of the lifted sections.  The
descent is therefore Mathlib's `CategoryTheory.GrothendieckTopology.Point.presheafFiberDesc`
precomposed with that comparison, and the germ formula is
`CategoryTheory.GrothendieckTopology.Point.toPresheafFiber_presheafFiberDesc`.  The target is
an additive group in the universe `max w m` in which the stalk is formed.

For a presheaf of modules `M₀` mapping locally bijectively to `F`, the fibre functor of a point
inverts the morphism (`CategoryTheory.GrothendieckTopology.Point.toPresheafFiber_map_bijective`),
and the descent is the one on `M₀` read through that bijection.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u m v w t

attribute [local instance] FinallySmall.preservesColimitsOfShape_of_isFiltered

namespace Stacks

section Ulift

variable {C : Type t} [Category.{v} C] (J : GrothendieckTopology C)
  {P Q : Cᵒᵖ ⥤ AddCommGrpCat.{m}} (ψ : P ⟶ Q)

/-- Raising the sections of presheaves of abelian groups to a larger universe does not change
whether a morphism between them is locally surjective. -/
instance isLocallySurjective_whiskerRight_uliftFunctor
    [Presheaf.IsLocallySurjective J ψ] :
    Presheaf.IsLocallySurjective J
      (Functor.whiskerRight ψ AddCommGrpCat.uliftFunctor.{w}) where
  imageSieve_mem {U} s := by
    have h : Presheaf.imageSieve
          (Functor.whiskerRight ψ AddCommGrpCat.uliftFunctor.{w}) s =
        Presheaf.imageSieve ψ s.down := by
      ext V i
      exact ⟨fun ⟨t, ht⟩ => ⟨t.down, congrArg ULift.down ht⟩,
        fun ⟨t, ht⟩ => ⟨ULift.up t, congrArg ULift.up ht⟩⟩
    rw [h]
    exact Presheaf.imageSieve_mem J ψ s.down

/-- Raising the sections of presheaves of abelian groups to a larger universe does not change
whether a morphism between them is locally injective. -/
instance isLocallyInjective_whiskerRight_uliftFunctor
    [Presheaf.IsLocallyInjective J ψ] :
    Presheaf.IsLocallyInjective J
      (Functor.whiskerRight ψ AddCommGrpCat.uliftFunctor.{w}) where
  equalizerSieve_mem {U} a b h := by
    have he : Presheaf.equalizerSieve
          (F := P ⋙ AddCommGrpCat.uliftFunctor.{w}) a b =
        Presheaf.equalizerSieve (F := P) a.down b.down := by
      ext V i
      exact ⟨fun hh => congrArg ULift.down hh, fun hh => congrArg ULift.up hh⟩
    rw [he]
    exact Presheaf.equalizerSieve_mem J ψ a.down b.down (congrArg ULift.down h)

end Ulift

variable {C : Type t} [Category.{v} C] [LocallySmall.{w} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (p : J.Point.{w}) (O : Sheaf J CommRingCat.{w})
  (F : SheafOfModules.{m} (commRingSheafToRingSheaf O))

/-! ### Descending a family of maps on the sections of an arbitrary presheaf -/

section LiftedDesc

variable {Q : Cᵒᵖ ⥤ AddCommGrpCat.{m}} {A : Type (max w m)} [AddCommGroup A]
  (φ : ∀ (U : C) (_x : p.fiber.obj U), Q.obj (op U) →+ A)
  (hφ : ∀ ⦃U V : C⦄ (f : U ⟶ V) (x : p.fiber.obj U) (s : Q.obj (op V)),
    φ U x (Q.map f.op s) = φ V (p.fiber.map f x) s)

/-- A family of additive maps out of the sections of a presheaf of abelian groups, read as a
family of morphisms out of its sections raised to the universe `max w m`. -/
noncomputable def liftedDescApp (U : C) (x : p.fiber.obj U) :
    (Q ⋙ AddCommGrpCat.uliftFunctor.{w}).obj (op U) ⟶ AddCommGrpCat.of A :=
  AddCommGrpCat.ofHom ((φ U x).comp (AddEquiv.ulift (α := Q.obj (op U))).toAddMonoidHom)

omit [LocallySmall.{w} C] [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
include hφ in
/-- A family of additive maps out of the sections of a presheaf of abelian groups which is
compatible with restriction gives a cocone on the lifted sections over the neighbourhoods
of `p`. -/
theorem liftedDescApp_w ⦃U V : C⦄ (f : U ⟶ V) (x : p.fiber.obj U) :
    (Q ⋙ AddCommGrpCat.uliftFunctor.{w}).map f.op ≫ liftedDescApp p φ U x =
      liftedDescApp p φ V (p.fiber.map f x) := by
  ext s
  exact hφ f x s.down

/-- The morphism out of the fibre of the lifted sections of a presheaf of abelian groups
determined by a compatible family of additive maps out of its sections. -/
noncomputable def liftedPresheafFiberDesc :
    (p.presheafFiber (A := AddCommGrpCat.{max w m})).obj
        (Q ⋙ AddCommGrpCat.uliftFunctor.{w}) ⟶ AddCommGrpCat.of A :=
  p.presheafFiberDesc (liftedDescApp p φ) (liftedDescApp_w p φ hφ)

omit [LocallySmall.{w} C] [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The descent along the fibre of the lifted sections sends the image of a section to the
value of the given family on it. -/
theorem toPresheafFiber_liftedPresheafFiberDesc (U : C) (x : p.fiber.obj U)
    (s : Q.obj (op U)) :
    liftedPresheafFiberDesc p φ hφ
        (p.toPresheafFiber U x (Q ⋙ AddCommGrpCat.uliftFunctor.{w}) (ULift.up s)) =
      φ U x s :=
  ConcreteCategory.congr_hom
    (p.toPresheafFiber_presheafFiberDesc (liftedDescApp p φ) (liftedDescApp_w p φ hφ) U x)
    (ULift.up s)

end LiftedDesc

/-- A map out of the stalk which is given on the germs `γ` of sections of a presheaf of modules
`M` by a compatible family `φ`, semilinear along `θ`, is semilinear along `θ`. -/
private theorem stalk_smul_of_germ {R' : Type*} [Ring R'] {A : Type*} [AddCommGroup A]
    [Module R' A] {M : PresheafOfModules.{m} (commRingSheafToRingSheaf O).obj}
    (γ : ∀ U : C, p.fiber.obj U → M.obj (op U) → moduleStalkLarge.{m} p O F)
    (D : moduleStalkLarge.{m} p O F →+ A) (φ : ∀ (U : C) (_x : p.fiber.obj U), M.obj (op U) →+ A)
    (θ : ((p.presheafFiber (A := CommRingCat.{w})).obj O.obj) →+* R')
    (hγ : ∀ z, ∃ (U : C) (x : p.fiber.obj U) (s : M.obj (op U)), γ U x s = z)
    (hγw : ∀ {U V : C} (f : U ⟶ V) (x : p.fiber.obj U) (s : M.obj (op V)),
      γ U x (M.map f.op s) = γ V (p.fiber.map f x) s)
    (hγsmul : ∀ (U : C) (x : p.fiber.obj U) (r : (commRingSheafToRingSheaf O).obj.obj (op U))
      (s : M.obj (op U)), γ U x (r • s) = p.toPresheafFiber U x O.obj r • γ U x s)
    (hD : ∀ (U : C) (x : p.fiber.obj U) (s : M.obj (op U)), D (γ U x s) = φ U x s)
    (hsmul : ∀ (U : C) (x : p.fiber.obj U)
      (r : (commRingSheafToRingSheaf O).obj.obj (op U)) (s : M.obj (op U)),
      φ U x (r • s) = θ (p.toPresheafFiber U x O.obj r) • φ U x s)
    (r : (p.presheafFiber (A := CommRingCat.{w})).obj O.obj) (z : moduleStalkLarge.{m} p O F) :
    D (r • z) = θ r • D z := by
  obtain ⟨U, xU, s, rfl⟩ := hγ z
  obtain ⟨V, yV, a, rfl⟩ := p.toPresheafFiber_jointly_surjective (P := O.obj) r
  obtain ⟨W, f, g, -⟩ :=
    IsCofilteredOrEmpty.cone_objs (p.fiber.elementsMk U xU) (p.fiber.elementsMk V yV)
  set a' : (commRingSheafToRingSheaf O).obj.obj (op W.1) := O.obj.map g.1.op a with ha'
  set s' : M.obj (op W.1) := M.map f.1.op s with hs'
  have hr : p.toPresheafFiber W.1 W.2 O.obj a' = p.toPresheafFiber V yV O.obj a := by
    rw [ha', p.toPresheafFiber_w_apply g.1 W.2 O.obj a, g.2]
  have hz : γ W.1 W.2 s' = γ U xU s := by rw [hs', hγw, f.2]
  calc D (p.toPresheafFiber V yV O.obj a • γ U xU s)
      = D (γ W.1 W.2 (a' • s')) := by rw [hγsmul, hr, hz]
    _ = θ (p.toPresheafFiber W.1 W.2 O.obj a') • D (γ W.1 W.2 s') := by rw [hD, hsmul, hD]
    _ = θ (p.toPresheafFiber V yV O.obj a) • D (γ U xU s) := by rw [hr, hz]

/-! ### Descending a family of maps on the sections of the sheaf itself -/

section Desc

variable {A : Type (max w m)} [AddCommGroup A]
  (φ : ∀ (U : C) (_x : p.fiber.obj U), F.val.obj (op U) →+ A)
  (hφ : ∀ ⦃U V : C⦄ (f : U ⟶ V) (x : p.fiber.obj U) (s : F.val.obj (op V)),
    φ U x (F.val.map f.op s) = φ V (p.fiber.map f x) s)

/-- The additive map out of the stalk of `F` at `p` determined by a family of additive maps
`F(U) →+ A`, one for each neighbourhood `(U, x)` of `p`, which is compatible with
restriction. -/
noncomputable def moduleStalkLargeDescOfCompatibleFamily : moduleStalkLarge.{m} p O F →+ A :=
  (liftedPresheafFiberDesc (Q := F.val.presheaf) p φ hφ).hom.comp
    (moduleStalkLargeFinalIso.{m} p O F).hom.hom

/-- The descended map sends the germ of a section over a neighbourhood to the value of the
given family on that section. -/
theorem moduleStalkLargeDescOfCompatibleFamily_germ (U : C) (x : p.fiber.obj U)
    (s : F.val.obj (op U)) :
    moduleStalkLargeDescOfCompatibleFamily p O F φ hφ (moduleStalkLargeGerm p O F U x s) =
      φ U x s := by
  have h : (moduleStalkLargeFinalIso.{m} p O F).hom
      ((moduleStalkLargeFinalIso.{m} p O F).inv
        (p.toPresheafFiber U x (liftedSectionPresheaf.{m} O F) (ULift.up s))) =
      p.toPresheafFiber U x (liftedSectionPresheaf.{m} O F) (ULift.up s) :=
    ConcreteCategory.congr_hom (moduleStalkLargeFinalIso.{m} p O F).inv_hom_id _
  show liftedPresheafFiberDesc (Q := F.val.presheaf) p φ hφ
    ((moduleStalkLargeFinalIso.{m} p O F).hom
      ((moduleStalkLargeFinalIso.{m} p O F).inv
        (p.toPresheafFiber U x (liftedSectionPresheaf.{m} O F) (ULift.up s)))) = _
  rw [h]
  exact toPresheafFiber_liftedPresheafFiberDesc (Q := F.val.presheaf) p φ hφ U x s

/-- If each member of the family is
semilinear along a ring map `θ` out of the fibre of `O` at `p`, then the descended map out of
the stalk is semilinear along `θ`. -/
theorem moduleStalkLargeDescOfCompatibleFamily_smul {R' : Type*} [Ring R'] [Module R' A]
    (θ : ((p.presheafFiber (A := CommRingCat.{w})).obj O.obj) →+* R')
    (hsmul : ∀ (U : C) (x : p.fiber.obj U)
      (r : (commRingSheafToRingSheaf O).obj.obj (op U)) (s : F.val.obj (op U)),
      φ U x (r • s) = θ (p.toPresheafFiber U x O.obj r) • φ U x s)
    (r : (p.presheafFiber (A := CommRingCat.{w})).obj O.obj)
    (z : moduleStalkLarge.{m} p O F) :
    moduleStalkLargeDescOfCompatibleFamily p O F φ hφ (r • z) =
      θ r • moduleStalkLargeDescOfCompatibleFamily p O F φ hφ z := by
  exact stalk_smul_of_germ p O F (M := F.val)
    (fun U x s => moduleStalkLargeGerm p O F U x s) _ φ θ
    (moduleStalkLargeGerm_jointly_surjective p O F) (moduleStalkLargeGerm_w p O F)
    (moduleStalkLargeGerm_smul p O F) (moduleStalkLargeDescOfCompatibleFamily_germ p O F φ hφ)
    hsmul r z

end Desc

/-- Two additive maps out of the stalk which agree on the germ of every section over every
neighbourhood are equal. -/
theorem moduleStalkLarge_addHom_ext {A : Type*} [AddCommGroup A]
    (f g : moduleStalkLarge.{m} p O F →+ A)
    (h : ∀ (U : C) (x : p.fiber.obj U) (s : F.val.obj (op U)),
      f (moduleStalkLargeGerm p O F U x s) = g (moduleStalkLargeGerm p O F U x s)) :
    f = g := by
  refine AddMonoidHom.ext fun z => ?_
  obtain ⟨U, x, s, rfl⟩ := moduleStalkLargeGerm_jointly_surjective p O F z
  exact h U x s

/-! ### Descending a family of maps on the sections of a presheaf of modules -/

section LocallyBijective

variable {M₀ : PresheafOfModules.{m} (commRingSheafToRingSheaf O).obj}
  (ψ : M₀.presheaf ⟶ F.val.presheaf)
  [Presheaf.IsLocallySurjective J ψ] [Presheaf.IsLocallyInjective J ψ]

omit [Presheaf.IsLocallyInjective J ψ] in
/-- Every element of the stalk of `F` at `p` is the germ of a section of a presheaf of modules
mapping locally surjectively to `F`. -/
theorem moduleStalkLargeGerm_exists_of_locallyBijective (z : moduleStalkLarge.{m} p O F) :
    ∃ (U : C) (x : p.fiber.obj U) (s : M₀.obj (op U)),
      moduleStalkLargeGerm p O F U x (ψ.app (op U) s) = z := by
  obtain ⟨U, x, t, rfl⟩ := moduleStalkLargeGerm_jointly_surjective p O F z
  obtain ⟨V, f, ⟨s, hs⟩, y, hy⟩ := p.jointly_surjective _
    (Presheaf.imageSieve_mem J ψ (U := op U) t) x
  refine ⟨V, y, s, ?_⟩
  rw [hs]
  exact (moduleStalkLargeGerm_w p O F f y t).trans
    (congrArg (fun z => moduleStalkLargeGerm p O F U z t) hy)

omit [Presheaf.IsLocallyInjective J ψ] in
/-- Two additive maps out of the stalk which agree on the germs of the sections of a presheaf
of modules mapping locally surjectively to `F` are equal. -/
theorem moduleStalkLarge_addHom_ext_of_locallyBijective {A : Type*} [AddCommGroup A]
    (f g : moduleStalkLarge.{m} p O F →+ A)
    (h : ∀ (U : C) (x : p.fiber.obj U) (s : M₀.obj (op U)),
      f (moduleStalkLargeGerm p O F U x (ψ.app (op U) s)) =
        g (moduleStalkLargeGerm p O F U x (ψ.app (op U) s))) :
    f = g := by
  refine AddMonoidHom.ext fun z => ?_
  obtain ⟨U, x, s, rfl⟩ := moduleStalkLargeGerm_exists_of_locallyBijective p O F ψ z
  exact h U x s

variable {A : Type (max w m)} [AddCommGroup A]
  (φ : ∀ (U : C) (_x : p.fiber.obj U), M₀.obj (op U) →+ A)
  (hφ : ∀ ⦃U V : C⦄ (f : U ⟶ V) (x : p.fiber.obj U) (s : M₀.obj (op V)),
    φ U x (M₀.map f.op s) = φ V (p.fiber.map f x) s)

/-- The bijection between the fibre at `p` of the lifted sections of a presheaf of modules and
the fibre of the lifted sections of its sheafification, as an additive equivalence. -/
noncomputable def liftedPresheafFiberEquiv :
    ((p.presheafFiber (A := AddCommGrpCat.{max w m})).obj
        (M₀.presheaf ⋙ AddCommGrpCat.uliftFunctor.{w}) : Type (max w m)) ≃+
      (p.presheafFiber (A := AddCommGrpCat.{max w m})).obj (liftedSectionPresheaf.{m} O F) :=
  letI : PreservesFilteredColimitsOfSize.{w, w} (forget AddCommGrpCat.{max w m}) :=
    preservesFilteredColimitsOfSize_shrink _
  AddEquiv.ofBijective
    ((p.presheafFiber (A := AddCommGrpCat.{max w m})).map
      (Functor.whiskerRight ψ AddCommGrpCat.uliftFunctor.{w})).hom
    (p.toPresheafFiber_map_bijective _)

/-- The comparison of the two fibres sends the image of a section of `M₀` to the image of its
image in `F`. -/
theorem liftedPresheafFiberEquiv_toPresheafFiber (U : C) (x : p.fiber.obj U)
    (s : M₀.obj (op U)) :
    liftedPresheafFiberEquiv p O F ψ
        (p.toPresheafFiber U x (M₀.presheaf ⋙ AddCommGrpCat.uliftFunctor.{w}) (ULift.up s)) =
      p.toPresheafFiber U x (liftedSectionPresheaf.{m} O F) (ULift.up (ψ.app (op U) s)) := by
  show ((p.presheafFiber (A := AddCommGrpCat.{max w m})).map
      (Functor.whiskerRight ψ AddCommGrpCat.uliftFunctor.{w}))
      (p.toPresheafFiber U x (M₀.presheaf ⋙ AddCommGrpCat.uliftFunctor.{w}) (ULift.up s)) = _
  exact ConcreteCategory.congr_hom
    (p.toPresheafFiber_naturality (Functor.whiskerRight ψ AddCommGrpCat.uliftFunctor.{w}) U x)
    (ULift.up s)

/-- The additive map out of the stalk of `F` at `p` determined by a family of additive maps out
of the sections of a presheaf of modules `M₀` mapping locally bijectively to `F`, one for each
neighbourhood of `p`, which is compatible with restriction. -/
noncomputable def moduleStalkLargeDescOfLocallyBijective : moduleStalkLarge.{m} p O F →+ A :=
  ((liftedPresheafFiberDesc (Q := M₀.presheaf) p φ hφ).hom.comp
    (liftedPresheafFiberEquiv p O F ψ).symm.toAddMonoidHom).comp
      (moduleStalkLargeFinalIso.{m} p O F).hom.hom

/-- The descended map sends the germ of the image of a section of `M₀` to the value of the
given family on that section. -/
theorem moduleStalkLargeDescOfLocallyBijective_germ (U : C) (x : p.fiber.obj U)
    (s : M₀.obj (op U)) :
    moduleStalkLargeDescOfLocallyBijective p O F ψ φ hφ
        (moduleStalkLargeGerm p O F U x (ψ.app (op U) s)) = φ U x s := by
  have hnat := liftedPresheafFiberEquiv_toPresheafFiber p O F ψ U x s
  have hfinal : (moduleStalkLargeFinalIso.{m} p O F).hom
      ((moduleStalkLargeFinalIso.{m} p O F).inv
        (p.toPresheafFiber U x (liftedSectionPresheaf.{m} O F)
          (ULift.up (ψ.app (op U) s)))) =
      p.toPresheafFiber U x (liftedSectionPresheaf.{m} O F) (ULift.up (ψ.app (op U) s)) :=
    ConcreteCategory.congr_hom (moduleStalkLargeFinalIso.{m} p O F).inv_hom_id _
  show liftedPresheafFiberDesc (Q := M₀.presheaf) p φ hφ
    ((liftedPresheafFiberEquiv p O F ψ).symm
      ((moduleStalkLargeFinalIso.{m} p O F).hom
        ((moduleStalkLargeFinalIso.{m} p O F).inv
          (p.toPresheafFiber U x (liftedSectionPresheaf.{m} O F)
            (ULift.up (ψ.app (op U) s)))))) = _
  rw [hfinal, ← hnat, (liftedPresheafFiberEquiv p O F ψ).symm_apply_apply]
  exact toPresheafFiber_liftedPresheafFiberDesc (Q := M₀.presheaf) p φ hφ U x s

/-- If `ψ` is linear and each member of the family is semilinear along a ring map `θ` out of the
fibre of `O` at `p`, then the descended map out of the stalk is semilinear along `θ`. -/
theorem moduleStalkLargeDescOfLocallyBijective_smul {R' : Type*} [Ring R'] [Module R' A]
    (θ : ((p.presheafFiber (A := CommRingCat.{w})).obj O.obj) →+* R')
    (hψ : ∀ (X : Cᵒᵖ) (r : (commRingSheafToRingSheaf O).obj.obj X) (s : M₀.obj X),
      ψ.app X (r • s) = r • ψ.app X s)
    (hsmul : ∀ (U : C) (x : p.fiber.obj U)
      (r : (commRingSheafToRingSheaf O).obj.obj (op U)) (s : M₀.obj (op U)),
      φ U x (r • s) = θ (p.toPresheafFiber U x O.obj r) • φ U x s)
    (r : (p.presheafFiber (A := CommRingCat.{w})).obj O.obj)
    (z : moduleStalkLarge.{m} p O F) :
    moduleStalkLargeDescOfLocallyBijective p O F ψ φ hφ (r • z) =
      θ r • moduleStalkLargeDescOfLocallyBijective p O F ψ φ hφ z := by
  refine stalk_smul_of_germ p O F (fun U x s => moduleStalkLargeGerm p O F U x (ψ.app (op U) s)) _
    φ θ (moduleStalkLargeGerm_exists_of_locallyBijective p O F ψ) (fun {U V} f x s => ?_)
    (fun U x r s => ?_) (moduleStalkLargeDescOfLocallyBijective_germ p O F ψ φ hφ) hsmul r z
  · exact (congrArg (moduleStalkLargeGerm p O F U x)
      (ConcreteCategory.congr_hom (ψ.naturality f.op) s)).trans
      (moduleStalkLargeGerm_w p O F f x _)
  · exact (congrArg (moduleStalkLargeGerm p O F U x) (hψ _ r s)).trans
      (moduleStalkLargeGerm_smul p O F U x r _)

end LocallyBijective

end Stacks

end
