module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.RingedToposOfAFibredCategory
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.RingedSites
public import StacksFrontier.CategoryTheory.Sites.Modules.UniverseLiftSheaf
public import StacksFrontier.CategoryTheory.Sites.Sheaf.HasSheafComposeForgetRing

/-!
# The small model of a ringed site, with its rings in the universe of the modules

The derived machinery for ringed sites in this library (`AlgebraicGeometry.RingedSite.{M, M, M}`)
is stated in a single universe: the objects, the morphisms and the section rings of the site all
in `M`, and the modules in `M` as well. A ringed site met in practice has a large underlying
category (objects in `Type (u + 1)`, morphisms in `Type u`) with rings in `u`, and its modules
are wanted in a universe `M` containing all of these. This file attaches to such a ringed site
`X` its *lift* `X↑`, a ringed site in the single universe `M`:

* the underlying category is the small model `AsSmall X.C`, equivalent to `X.C`;
* the topology is the one induced along that equivalence, so that both functors of the
  equivalence are continuous;
* the structure sheaf is `U ↦ ULift (O_X(U))`, the structure sheaf of `X` with its section rings
  raised to the universe `M`.

Sheaves of modules on `X` and on `X↑` are then identified by the ring transport
`Stacks.UniverseLift.RingTransport.sheafEquivalence` attached to the equivalence of categories
and the ring isomorphisms `ULift (O_X(U)) ≃+* O_X(U)`.

## Main definitions

* `Stacks.UniverseLift.liftTopology`: the topology on `AsSmall C` induced by a topology on `C`.
* `Stacks.UniverseLift.liftCommRingSheaf`: a sheaf of commutative rings on `C`, carried to
  `AsSmall C` with its section rings raised to a larger universe.
* `AlgebraicGeometry.RingedSite.lift`: the lift `X↑` of a ringed site.
* `AlgebraicGeometry.RingedSite.liftRingTransport`: the ring transport from `X` to `X↑`.

## Main results

* `Stacks.UniverseLift.isSheaf_comp_commRingCatULift`: raising the universe of the section
  rings of a sheaf of commutative rings gives a sheaf, on an arbitrary site.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w z z' w' u v r

namespace Stacks.UniverseLift

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- The topology on the small model `AsSmall C` induced by a topology `J` on `C` along the
equivalence `AsSmall.down : AsSmall C ⥤ C`. -/
abbrev liftTopology : GrothendieckTopology (AsSmall.{w} C) :=
  (AsSmall.down : AsSmall.{w} C ⥤ C).inducedTopology J

/-- `AsSmall.down` is continuous for the induced topology. -/
instance asSmallDown_isContinuous :
    (AsSmall.down : AsSmall.{w} C ⥤ C).IsContinuous (liftTopology.{w} J) J :=
  inferInstanceAs ((AsSmall.equiv (C := C)).inverse.IsContinuous
    ((AsSmall.equiv (C := C)).inverse.inducedTopology J) J)

/-- `AsSmall.up` is continuous for the induced topology. -/
instance asSmallUp_isContinuous :
    (AsSmall.up : C ⥤ AsSmall.{w} C).IsContinuous J (liftTopology.{w} J) :=
  inferInstanceAs ((AsSmall.equiv (C := C)).functor.IsContinuous J
    ((AsSmall.equiv (C := C)).inverse.inducedTopology J))

variable {J}

/-- **Raising the universe of the section rings of a sheaf of commutative rings gives a
sheaf**, on an arbitrary site. The sheaf condition of a presheaf of commutative rings is
detected on underlying sets (`CategoryTheory.Presheaf.isSheaf_of_isSheaf_comp_forget_commRingCat`),
where the universe lift is that of types, which preserves limits; and a sheaf of commutative
rings has a sheaf of underlying sets, the forgetful functor of rings being corepresentable. -/
theorem isSheaf_comp_commRingCatULift (P : Cᵒᵖ ⥤ CommRingCat.{r}) (hP : Presheaf.IsSheaf J P) :
    Presheaf.IsSheaf J (P ⋙ AlgebraicGeometry.SheafOfModules.commRingCatULift.{r, z}) := by
  apply Presheaf.isSheaf_of_isSheaf_comp_forget_commRingCat
  have h₁ : Presheaf.IsSheaf J (P ⋙ forget₂ CommRingCat RingCat) :=
    GrothendieckTopology.HasSheafCompose.isSheaf P hP
  have h₂ : Presheaf.IsSheaf J ((P ⋙ forget₂ CommRingCat RingCat) ⋙ forget RingCat) :=
    GrothendieckTopology.HasSheafCompose.isSheaf _ h₁
  have h₃ := Presheaf.isSheaf_comp_of_isSheaf J _ CategoryTheory.uliftFunctor.{z, r} h₂
  exact (Presheaf.isSheaf_of_iso_iff (NatIso.ofComponents (fun _ ↦ Iso.refl _))).1 h₃

/-- A sheaf of commutative rings on `C`, carried along an equivalence `e : C ≌ D` to `D` (with
the topology induced along `e.inverse`) and with its section rings raised by the universe lift
`AlgebraicGeometry.SheafOfModules.commRingCatULift`. -/
noncomputable def transportCommRingSheaf {D : Type z'} [Category.{w'} D] (e : C ≌ D)
    (O : Sheaf J CommRingCat.{r}) :
    Sheaf (e.inverse.inducedTopology J) CommRingCat.{max r z} :=
  ⟨e.inverse.op ⋙ O.obj ⋙ AlgebraicGeometry.SheafOfModules.commRingCatULift.{r, z},
    isSheaf_comp_commRingCatULift _ (e.inverse.op_comp_isSheaf (e.inverse.inducedTopology J) J O)⟩

/-- A sheaf of commutative rings on `C`, carried to the small model `AsSmall C` along the
equivalence and with its section rings raised by the universe lift
`AlgebraicGeometry.SheafOfModules.commRingCatULift`. -/
noncomputable def liftCommRingSheaf (O : Sheaf J CommRingCat.{r}) :
    Sheaf (liftTopology.{w} J) CommRingCat.{max r z} :=
  transportCommRingSheaf.{z} (AsSmall.equiv : C ≌ AsSmall.{w} C) O

end Stacks.UniverseLift

namespace AlgebraicGeometry.RingedSite

open Stacks.UniverseLift

/-- **The transport of a ringed site along an equivalence of its underlying category**, with
its section rings raised to a larger universe. For a ringed site `X` and an equivalence
`e : X.C ≌ D`, this is the ringed site with underlying category `D`, the topology induced along
`e.inverse`, and the structure sheaf `V ↦ ULift (O_X(e⁻¹ V))`. -/
noncomputable abbrev transport (X : RingedSite.{u, v, r}) {D : Type z'} [Category.{w'} D]
    (e : X.C ≌ D) : RingedSite.{z', w', max r z} where
  C := D
  J := e.inverse.inducedTopology X.J
  O := transportCommRingSheaf.{z} e X.O

/-- The ring transport from a ringed site to its transport along an equivalence `e`: the section
rings `ULift (O_X(e⁻¹ V))` of the transported structure sheaf are identified with the section
rings `O_X(e⁻¹ V)` by `ULift.ringEquiv`. -/
noncomputable def transportRingTransport (X : RingedSite.{u, v, r}) {D : Type z'}
    [Category.{w'} D] (e : X.C ≌ D) :
    RingTransport e (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (transport.{z} X e).O).obj where
  iso _ := ULift.ringEquiv
  naturality _ _ := rfl

/-- The inverse of the equivalence `X.C ≌ D` is continuous for the transported topology. -/
instance transport_inverse_isContinuous (X : RingedSite.{u, v, r}) {D : Type z'}
    [Category.{w'} D] (e : X.C ≌ D) : e.inverse.IsContinuous (transport.{z} X e).J X.J :=
  inferInstanceAs (e.inverse.IsContinuous (e.inverse.inducedTopology X.J) X.J)

/-- The functor of the equivalence `X.C ≌ D` is continuous for the transported topology. -/
instance transport_functor_isContinuous (X : RingedSite.{u, v, r}) {D : Type z'}
    [Category.{w'} D] (e : X.C ≌ D) : e.functor.IsContinuous X.J (transport.{z} X e).J :=
  inferInstanceAs (e.functor.IsContinuous X.J (e.inverse.inducedTopology X.J))

/-- The inverse of the equivalence `X.C ≌ D` is a dense subsite inclusion for the transported
topology. -/
instance transport_inverse_isDenseSubsite (X : RingedSite.{u, v, r}) {D : Type z'}
    [Category.{w'} D] (e : X.C ≌ D) : e.inverse.IsDenseSubsite (transport.{z} X e).J X.J :=
  inferInstanceAs (e.inverse.IsDenseSubsite (e.inverse.inducedTopology X.J) X.J)

/-- The functor of the equivalence `X.C ≌ D` is a dense subsite inclusion for the transported
topology. -/
instance transport_functor_isDenseSubsite (X : RingedSite.{u, v, r}) {D : Type z'}
    [Category.{w'} D] (e : X.C ≌ D) : e.functor.IsDenseSubsite X.J (transport.{z} X e).J :=
  inferInstanceAs (e.functor.IsDenseSubsite X.J (e.inverse.inducedTopology X.J))

/-- **The lift of a ringed site to a single universe.** For a ringed site `X` whose underlying
category has objects in `u` and morphisms in `v` and whose section rings are in `r`, its lift is
the ringed site in the universe `M = max u v r w` with underlying category the small model
`AsSmall X.C`, the induced topology, and the structure sheaf `U ↦ ULift (O_X(U))`: the transport
of `X` along `AsSmall.equiv`. -/
noncomputable abbrev lift (X : RingedSite.{u, v, r}) :
    RingedSite.{max u v r w, max u v r w, max u v r w} :=
  transport.{max u v w} X (AsSmall.equiv : X.C ≌ AsSmall.{max r w} X.C)

/-- The underlying category of the lift is the small model of the underlying category. -/
lemma lift_C (X : RingedSite.{u, v, r}) : (lift.{w} X).C = AsSmall.{max r w} X.C := rfl

/-- The topology of the lift is the induced topology. -/
lemma lift_J (X : RingedSite.{u, v, r}) : (lift.{w} X).J = liftTopology.{max r w} X.J := rfl

/-- The ring transport from a ringed site to its lift: along the equivalence
`X.C ≌ AsSmall X.C`, the section rings `ULift (O_X(U))` of the lifted structure sheaf are
identified with the section rings `O_X(U)` by `ULift.ringEquiv`. -/
noncomputable def liftRingTransport (X : RingedSite.{u, v, r}) :
    RingTransport (AsSmall.equiv : X.C ≌ (lift.{w} X).C)
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (lift.{w} X).O).obj :=
  transportRingTransport.{max u v w} X AsSmall.equiv

/-- The inverse of the equivalence `X.C ≌ X↑.C` is continuous. -/
instance lift_asSmallDown_isContinuous (X : RingedSite.{u, v, r}) :
    (AsSmall.equiv : X.C ≌ (lift.{w} X).C).inverse.IsContinuous (lift.{w} X).J X.J :=
  asSmallDown_isContinuous.{max r w} X.J

/-- The functor of the equivalence `X.C ≌ X↑.C` is continuous. -/
instance lift_asSmallUp_isContinuous (X : RingedSite.{u, v, r}) :
    (AsSmall.equiv : X.C ≌ (lift.{w} X).C).functor.IsContinuous X.J (lift.{w} X).J :=
  asSmallUp_isContinuous.{max r w} X.J

/-- The inverse of the equivalence `X.C ≌ X↑.C` is a dense subsite inclusion. -/
instance lift_asSmallDown_isDenseSubsite (X : RingedSite.{u, v, r}) :
    (AsSmall.equiv : X.C ≌ (lift.{w} X).C).inverse.IsDenseSubsite (lift.{w} X).J X.J :=
  transport_inverse_isDenseSubsite.{max u v w} X AsSmall.equiv

/-- The functor of the equivalence `X.C ≌ X↑.C` is a dense subsite inclusion. -/
instance lift_asSmallUp_isDenseSubsite (X : RingedSite.{u, v, r}) :
    (AsSmall.equiv : X.C ≌ (lift.{w} X).C).functor.IsDenseSubsite X.J (lift.{w} X).J :=
  transport_functor_isDenseSubsite.{max u v w} X AsSmall.equiv

/-- **Sheaves of modules on a ringed site and on its lift agree**, at every module universe:
the equivalence of `Stacks.UniverseLift.RingTransport.sheafEquivalence` for the ring transport
`AlgebraicGeometry.RingedSite.liftRingTransport`. -/
noncomputable def liftModulesEquivalence (X : RingedSite.{u, v, r}) :
    SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ≌
      SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf (lift.{w} X).O) :=
  (liftRingTransport.{w} X).sheafEquivalence

end AlgebraicGeometry.RingedSite
