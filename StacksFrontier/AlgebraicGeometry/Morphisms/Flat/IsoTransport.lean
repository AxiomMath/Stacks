module

public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.Topology.Sheaves.Functors.Module.SemilinearStalk
public import StacksFrontier.Topology.Sheaves.Modules.Colimits

/-!
# Flatness over the base depends only on the isomorphism class of the module

For a morphism of ringed spaces `p : X ⟶ Y`, an `𝒪_X`-module flat over `Y` at a point stays
flat over `Y` at that point after replacing it by an isomorphic module. The reason is that
`AlgebraicGeometry.IsFlatOverAt` is flatness of a single stalk over a single ring, and an
isomorphism of modules induces an isomorphism on stalks which is linear for the structure
sheaf, hence a fortiori for the scalars restricted along the stalk map of `p`.

The only delicate point is that the stalk of a sheaf of modules is linear over the stalk of
the structure sheaf read in `RingCat`, whereas the stalk map of `p` lands in the stalk read in
`CommRingCat`; `AlgebraicGeometry.SemilinearStalk.commStalkRingEquiv` compares the two, and
`AlgebraicGeometry.comm_smul_eq_universe` says the comparison does not change the action.

Everything here is stated for ringed spaces. That also covers schemes: for `f : X ⟶ S` a
morphism of schemes and `F G : X.Modules`, the type `X.Modules` is by definition the type of
sheaves of modules on the underlying ringed space of `X`, so
`AlgebraicGeometry.isFlatOverAt_iff_of_moduleIso` applies to `f.toLRSHom.toShHom` and an
isomorphism `F ≅ G` with no bridging.

## Main results

* `AlgebraicGeometry.isFlatOverAt_of_moduleIso`: flatness over the base at a point transfers
  along an isomorphism of modules.
* `AlgebraicGeometry.isFlatOverAt_iff_of_moduleIso` and
  `AlgebraicGeometry.isFlatOver_iff_of_moduleIso`: the pointwise and global biconditional
  forms.

## References

* [Stacks Project, Tag 08KT](https://stacks.math.columbia.edu/tag/08KT)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- Taking the germ of a scalar in the commutative structure presheaf and acting on the germ of
a section agrees with acting through the germ taken in the underlying presheaf of rings. -/
private theorem comm_smul_germ_universe {X : TopCat.{u}}
    (R : TopCat.Presheaf CommRingCat.{u} X) (x : X)
    (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}))
    (U : TopologicalSpace.Opens X) (hx : x ∈ U)
    (r : R.obj (Opposite.op U)) (m : M.obj (Opposite.op U)) :
    R.germ U x hx r • TopCat.Presheaf.germ M.presheaf U x hx m =
      TopCat.Presheaf.germ (C := RingCat.{u})
        (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}) U x hx r •
        TopCat.Presheaf.germ M.presheaf U x hx m := by
  rw [← PresheafOfModules.germ_smul M x U hx r m]
  exact PresheafOfModules.germ_ringCat_smul M x U hx r m

/-- Transporting a stalk scalar along the comparison between the stalk of the commutative
structure presheaf and the stalk of its underlying presheaf of rings does not change the
action on the module stalk. -/
private theorem comm_smul_eq_universe {X : TopCat.{u}}
    (R : TopCat.Presheaf CommRingCat.{u} X) (x : X)
    (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}))
    (s : TopCat.Presheaf.stalk (C := RingCat.{u})
      (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}) x)
    (m : TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.presheaf x) :
    SemilinearStalk.commStalkRingEquiv R x s • m = s • m := by
  obtain ⟨U₁, hU₁, r₀, hr⟩ := TopCat.Presheaf.exists_germ_eq
    (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}) s
  obtain ⟨U₂, hU₂, m₀, hm⟩ := TopCat.Presheaf.exists_germ_eq M.presheaf m
  have hmem : x ∈ U₁ ⊓ U₂ := ⟨hU₁, hU₂⟩
  rw [← hr, ← hm, ← TopCat.Presheaf.germ_res_apply (R ⋙ forget₂ CommRingCat.{u} RingCat.{u})
      (homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁)) x hmem r₀,
    ← TopCat.Presheaf.germ_res_apply M.presheaf
      (homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂)) x hmem m₀,
    SemilinearStalk.commStalkRingEquiv_germ]
  exact comm_smul_germ_universe R x M (U₁ ⊓ U₂) hmem
    ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).map (homOfLE inf_le_left).op r₀)
    (M.presheaf.map (homOfLE inf_le_right).op m₀)

/-- Flatness over the base at a point transfers along an isomorphism of modules. -/
theorem isFlatOverAt_of_moduleIso {X Y : AlgebraicGeometry.RingedSpace.{u, u}} (p : X ⟶ Y)
    {F G : SheafOfModules.{u} ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf)}
    (e : F ≅ G) (x : X) (hF : IsFlatOverAt p F x) : IsFlatOverAt p G x := by
  let M : PresheafOfModules.{u}
      (X.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}) := F.val
  let N : PresheafOfModules.{u}
      (X.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}) := G.val
  let : Module (Y.presheaf.stalk (p.hom.base x))
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.presheaf x) :=
    Module.compHom _ (p.hom.stalkMap x).hom
  let : Module (Y.presheaf.stalk (p.hom.base x))
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) N.presheaf x) :=
    Module.compHom _ (p.hom.stalkMap x).hom
  let e' := ((SheafOfModules.stalkFunctor _ x).mapIso e).toLinearEquiv
  let e'' : (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.presheaf x)
      ≃ₗ[Y.presheaf.stalk (p.hom.base x)]
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) N.presheaf x) :=
    { e'.toAddEquiv with
      map_smul' := by
        intro r m
        obtain ⟨s, hs⟩ := (SemilinearStalk.commStalkRingEquiv X.presheaf x).surjective
          ((p.hom.stalkMap x).hom r)
        have hFsmul := comm_smul_eq_universe X.presheaf x F.val s m
        let em : TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) N.presheaf x := e' m
        have hGsmul := comm_smul_eq_universe X.presheaf x G.val s em
        rw [hs] at hFsmul hGsmul
        change e' (((p.hom.stalkMap x).hom r) • m) =
          ((p.hom.stalkMap x).hom r) • em
        rw [hFsmul, hGsmul]
        exact e'.map_smul s m }
  exact Module.Flat.of_linearEquiv e''.symm

/-- Flatness over the base at a point depends only on the isomorphism class of the module. -/
theorem isFlatOverAt_iff_of_moduleIso {X Y : AlgebraicGeometry.RingedSpace.{u, u}} (p : X ⟶ Y)
    {F G : SheafOfModules.{u} ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf)}
    (e : F ≅ G) (x : X) : IsFlatOverAt p F x ↔ IsFlatOverAt p G x :=
  ⟨isFlatOverAt_of_moduleIso p e x, isFlatOverAt_of_moduleIso p e.symm x⟩

/-- Flatness over the base depends only on the isomorphism class of the module. -/
theorem isFlatOver_iff_of_moduleIso {X Y : AlgebraicGeometry.RingedSpace.{u, u}} (p : X ⟶ Y)
    {F G : SheafOfModules.{u} ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf)}
    (e : F ≅ G) : IsFlatOver p F ↔ IsFlatOver p G :=
  forall_congr' fun x ↦ isFlatOverAt_iff_of_moduleIso p e x

end AlgebraicGeometry
