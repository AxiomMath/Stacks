module

public import StacksFrontier.Topology.Sheaves.Sheafify.ModuleStalkTensor
public import StacksFrontier.Topology.Sheaves.Functors.Module.SemilinearStalk
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The stalks of a pullback of sheaves of modules

Let `(f, f^\sharp) : (X, O_X) → (Y, O_Y)` be a morphism of ringed spaces and let `G` be a
sheaf of `O_Y`-modules.  Stacks Tag 0098 says that for `x : X`

  `(f^*G)_x = G_{f(x)} ⊗_{O_{Y,f(x)}} O_{X,x}`

as `O_{X,x}`-modules, the tensor product being taken along
`f^\sharp_x : O_{Y,f(x)} → O_{X,x}`.

Following Stacks Tag 0095, the pullback is the tensor product
`f^*G = O_X ⊗_{f^{-1}O_Y} f^{-1}G`.

## Main definitions

* `PullbackStalkTensor.invRing`, `PullbackStalkTensor.invMod`: `f^{-1}O_Y` as a sheaf of
  commutative rings and `f^{-1}G` as a sheaf of `f^{-1}O_Y`-modules.  The latter is Stacks
  008X's inverse image, whose base is transported along `ringSheafInvRingIso`.
* `PullbackStalkTensor.ringSheafInvRingIso`: the isomorphism between the underlying sheaf of
  (not necessarily commutative) rings of `f^{-1}O_Y` and the `RingCat`-level inverse image
  of Stacks 008X.
* `PullbackStalkTensor.stalkRingEquiv`: the ring equivalence `O_{Y,f(x)} ≃+* (f^{-1}O_Y)_x`.

## Main results

* `PullbackStalkTensor.stalkAddEquiv_smul`: the additive identification
  `G_{f(x)} ≅ (f^{-1}G)_x` is semilinear over `stalkRingEquiv`.
* `PullbackStalkTensor.stalkPullbackTensorIso`: the `O_{X,x}`-linear equivalence
  `G_{f(x)} ⊗_{O_{Y,f(x)}} O_{X,x} ≃ₗ (f^*G)_x` (Stacks Tag 0098).

## Notes on interpretation

* As in Tag 008B, the Stacks Project's `=` is a canonical isomorphism; we produce an
  `O_{X,x}`-linear equivalence.
* The structure morphism is taken in its adjoint form `f^{-1}O_Y ⟶ O_X`, which is what
  Stacks 0095 uses ("the ring map `f^{-1}O_Y → O_X` is the map corresponding to
  `f^\sharp`").
* `srcMod`/`tgtMod` are retypings of `G.val` and `(f^{-1}G).val` (definitionally equal to
  them) whose base presheaf of rings is spelled `· ⋙ forget₂ CommRingCat RingCat`, so that
  Mathlib's `CommRingCat`-stalk module instance is found by instance synthesis. The same
  retyping for the target of the main isomorphism is recorded once and for all as the instance
  `Stacks.Sheafify.ModuleStalkTensor.tensorSheafStalkModule`; without it the statement of
  `stalkPullbackTensorIso` does not elaborate, because the base of
  `(tensorSheaf …).val` is `O_X ⋙ forget₂ CommRingCat RingCat` only after unfolding
  `CategoryTheory.sheafCompose`, which typeclass resolution will not do.

## Implementation notes

**Universes.** Everything is stated at a single universe `u` carrying the space, the rings
and the module sections together, so the tagged statement applies to a morphism of ringed
spaces over `TopCat.{u}` — in particular to a morphism of `Scheme.{u}`.  That single
universe is forced, not chosen, and the two constraints forcing it both come from Mathlib:
`TopCat.Presheaf.pullback` asks for the hom universe of the target category to be the
universe of the space, so `CommRingCat.{v}` on a space in `TopCat.{u}` forces `v = u`; and
`PresheafOfModules.ModuleColimit` (which computes the pullback module structure upstream)
ties the module universe and the smallness universe to the ring universe.  Full independence
of the space and ring universes is therefore not available here.  Every `TopCat`,
`CommRingCat`, `RingCat`, `Ab`, `PresheafOfModules` and `SheafOfModules` argument is written
`.{u}` explicitly: left implicit they default to `0` and silently pin the whole file there.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Limits Opposite Stacks.PresheafOfModules.Pullback
  SemilinearStalk
  Stacks.Sheafify.ModuleStalkTensor InverseImageModules

universe u

namespace PullbackStalkTensor

variable {X Y : TopCat.{u}} (f : X ⟶ Y) (OY : TopCat.Sheaf CommRingCat.{u} Y)

/-- The presheaf pullback `f_p O_Y`, formed in `CommRingCat`. -/
noncomputable def pullbackRingComm : TopCat.Presheaf CommRingCat.{u} X :=
  (TopCat.Presheaf.pullback CommRingCat.{u} f).obj OY.obj

/-- `f^{-1}O_Y` as a sheaf of commutative rings on `X`: the sheafification of `f_p O_Y`. -/
noncomputable def invRing : TopCat.Sheaf CommRingCat.{u} X :=
  (presheafToSheaf (Opens.grothendieckTopology X) CommRingCat.{u}).obj (pullbackRingComm f OY)

/-- The isomorphism between the underlying sheaf of (not necessarily commutative) rings of
`f^{-1}O_Y` and the `RingCat`-level inverse image of Stacks 008X, given by the preservation by
`forget₂ CommRingCat RingCat` of the left Kan extension computing `f_p` and of the
sheafification. -/
noncomputable def ringSheafInvRingIso :
    ringSheaf (invRing f OY) ≅ inverseImageRing f (ringSheaf OY) :=
  ((sheafComposeNatIso (Opens.grothendieckTopology X) (forget₂ CommRingCat.{u} RingCat.{u})
      (sheafificationAdjunction _ CommRingCat.{u})
      (sheafificationAdjunction _ RingCat.{u})).app (pullbackRingComm f OY)).symm ≪≫
  (presheafToSheaf (Opens.grothendieckTopology X) RingCat.{u}).mapIso
    ((Functor.lanCompIsoOfPreserves (forget₂ CommRingCat.{u} RingCat.{u})
      (Opens.map f).op).app OY.obj)

variable (G : SheafOfModules.{u} (ringSheaf OY))

/-- `f^{-1}G` as a sheaf of `f^{-1}O_Y`-modules: Stacks 008X's inverse image, with its base
transported along `ringSheafInvRingIso`. -/
noncomputable def invMod : SheafOfModules.{u} (ringSheaf (invRing f OY)) where
  val := (PresheafOfModules.restrictScalars (ringSheafInvRingIso f OY).hom.hom).obj
    (inverseImageSheafOfModules f (ringSheaf OY) G).val
  isSheaf := (inverseImageSheafOfModules f (ringSheaf OY) G).isSheaf

/-- `O_{Y,f x} ≅ (f⁻¹O_Y)_x`, at the level of underlying rings. -/
noncomputable def ringStalkIso (x : X) :
    TopCat.Presheaf.stalk (C := RingCat.{u})
        (OY.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}) (f x) ≅
      TopCat.Presheaf.stalk (C := RingCat.{u})
        ((invRing f OY).obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}) x :=
  invRingStalkIso f (ringSheaf OY) x ≪≫
    ((TopCat.Presheaf.stalkFunctor RingCat.{u} x).mapIso
      ((sheafToPresheaf (Opens.grothendieckTopology X) RingCat.{u}).mapIso
        (ringSheafInvRingIso f OY))).symm

/-- The ring equivalence `O_{Y,f x} ≃+* (f⁻¹O_Y)_x`. -/
noncomputable def stalkRingEquiv (x : X) :
    ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u}) OY.obj (f x)) ≃+*
      ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u}) (invRing f OY).obj x) :=
  (commStalkRingEquiv OY.obj (f x)).symm.trans
    (((ringStalkIso f OY x).ringCatIsoToRingEquiv).trans
      (commStalkRingEquiv (invRing f OY).obj x))


/-- `G.val`, retyped so that instance synthesis sees its base as `OY ⋙ forget₂`. -/
noncomputable def srcMod : PresheafOfModules.{u} (OY.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}) :=
  G.val

/-- `(f⁻¹G).val`, retyped so that instance synthesis sees its base as
`(f⁻¹O_Y) ⋙ forget₂`. -/
noncomputable def tgtMod :
    PresheafOfModules.{u} ((invRing f OY).obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}) :=
  (invMod f OY G).val

/-- `G_{f x} ≅ (f⁻¹G)_x` as an additive equivalence (Stacks 008O(2) for `G`). -/
noncomputable def stalkAddEquiv (x : X) :
    ToType (TopCat.Presheaf.stalk (C := Ab.{u}) (srcMod OY G).presheaf (f x)) ≃+
      ToType (TopCat.Presheaf.stalk (C := Ab.{u}) (tgtMod f OY G).presheaf x) :=
  (invModStalkIso f (ringSheaf OY) G x).addCommGroupIsoToAddEquiv

/-- The isomorphism of stalks at `x` induced by `ringSheafInvRingIso`. -/
noncomputable def bridgeStalkIso (x : X) :
    TopCat.Presheaf.stalk (C := RingCat.{u})
        ((invRing f OY).obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}) x ≅
      TopCat.Presheaf.stalk (C := RingCat.{u}) (inverseImageRing f (ringSheaf OY)).obj x :=
  (TopCat.Presheaf.stalkFunctor RingCat.{u} x).mapIso
    ((sheafToPresheaf (Opens.grothendieckTopology X) RingCat.{u}).mapIso
      (ringSheafInvRingIso f OY))

/-- The forward map of `bridgeStalkIso` is the stalk map of `ringSheafInvRingIso`. -/
theorem bridgeStalkIso_hom (x : X) :
    (bridgeStalkIso f OY x).hom = ringStalkMap (ringSheafInvRingIso f OY).hom.hom x := rfl

/-- Elementwise, `ringStalkIso` is the Stacks 008X stalk identification `invRingStalkIso`
followed by the inverse of `bridgeStalkIso`. -/
theorem ringStalkIso_hom_eq (x : X)
    (s : TopCat.Presheaf.stalk (C := RingCat.{u})
      (OY.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}) (f x)) :
    (ringStalkIso f OY x).hom s
      = (bridgeStalkIso f OY x).inv ((invRingStalkIso f (ringSheaf OY) x).hom s) := rfl

/-- The additive identification
`G_{f x} ≅ (f^{-1}G)_x` carries the `O_{Y,f x}`-action to the `(f^{-1}O_Y)_x`-action along the
ring equivalence `stalkRingEquiv`. -/
theorem stalkAddEquiv_smul (x : X)
    (a : ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u}) OY.obj (f x)))
    (m : ToType (TopCat.Presheaf.stalk (C := Ab.{u}) (srcMod OY G).presheaf (f x))) :
    stalkAddEquiv f OY G x (a • m)
      = stalkRingEquiv f OY x a • stalkAddEquiv f OY G x m := by
  set s := (commStalkRingEquiv OY.obj (f x)).symm a with hs
  set ψ := (invModStalkIso f (ringSheaf OY) G x).hom with hψ
  have h1 : a • m = s • m := by
    rw [← comm_smul_eq OY.obj (f x) (srcMod OY G) s m, hs, RingEquiv.apply_symm_apply]
  have h2 : ψ (s • m) = (invRingStalkIso f (ringSheaf OY) x).hom s • ψ m :=
    invModStalkIso_smul f (ringSheaf OY) G x s m
  have h3 : ringStalkMap (ringSheafInvRingIso f OY).hom.hom x ((ringStalkIso f OY x).hom s)
      = (invRingStalkIso f (ringSheaf OY) x).hom s :=
    (bridgeStalkIso f OY x).inv_hom_id_apply _
  have step1 : stalkRingEquiv f OY x a • stalkAddEquiv f OY G x m
      = ((ringStalkIso f OY x).hom s) • stalkAddEquiv f OY G x m :=
    comm_smul_eq (invRing f OY).obj x (tgtMod f OY G) ((ringStalkIso f OY x).hom s)
      (stalkAddEquiv f OY G x m)
  have step2 : ((ringStalkIso f OY x).hom s) • stalkAddEquiv f OY G x m
      = ringStalkMap (ringSheafInvRingIso f OY).hom.hom x ((ringStalkIso f OY x).hom s) • ψ m :=
    restrictScalars_stalk_smul (ringSheafInvRingIso f OY).hom.hom
      (inverseImageSheafOfModules f (ringSheaf OY) G).val x
      ((ringStalkIso f OY x).hom s) (ψ m)
  rw [h1, step1, step2, h3]
  exact h2


variable (OX : TopCat.Sheaf CommRingCat.{u} X) (alpha : invRing f OY ⟶ OX)

/-- The ring map `f^\sharp_x : O_{Y, f(x)} → O_{X, x}`: the identification
`O_{Y,f(x)} ≅ (f^{-1}O_Y)_x` followed by the stalk of the structure morphism
`f^{-1}O_Y → O_X`. -/
noncomputable def sharpStalk (x : X) :
    ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u}) OY.obj (f x)) →+*
      ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u}) OX.obj x) :=
  (stalkHomOfSheaves (invRing f OY) OX alpha x).hom.comp (stalkRingEquiv f OY x)

section Semilinear

variable (x : X)

/-- The ring homomorphism underlying `stalkRingEquiv`. -/
@[reducible] noncomputable def stalkRingHom :
    ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u}) OY.obj (f x)) →+*
      ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u}) (invRing f OY).obj x) :=
  (stalkRingEquiv f OY x : _ →+* _)

/-- The ring homomorphism underlying the inverse of `stalkRingEquiv`. -/
@[reducible] noncomputable def stalkRingHomSymm :
    ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u}) (invRing f OY).obj x) →+*
      ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u}) OY.obj (f x)) :=
  ((stalkRingEquiv f OY x).symm : _ →+* _)

/-- `stalkRingHom` and `stalkRingHomSymm` are mutually inverse, coming from a ring
equivalence. -/
instance : RingHomInvPair (stalkRingHom f OY x) (stalkRingHomSymm f OY x) :=
  RingHomInvPair.of_ringEquiv (stalkRingEquiv f OY x)

/-- The `RingHomInvPair` of `stalkRingHom` and `stalkRingHomSymm` in the other order. -/
instance : RingHomInvPair (stalkRingHomSymm f OY x) (stalkRingHom f OY x) :=
  RingHomInvPair.symm (stalkRingHom f OY x) (stalkRingHomSymm f OY x)

/-- `G_{f x} ≃ (f⁻¹G)_x`, semilinear over `stalkRingEquiv`. -/
noncomputable def stalkSemilinearEquiv :
    ToType (TopCat.Presheaf.stalk (C := Ab.{u}) (srcMod OY G).presheaf (f x)) ≃ₛₗ[
        stalkRingHom f OY x]
      ToType (TopCat.Presheaf.stalk (C := Ab.{u}) (tgtMod f OY G).presheaf x) :=
  { stalkAddEquiv f OY G x with
    map_smul' := stalkAddEquiv_smul f OY G x }

/-- The identity of `O_{X,x}`, semilinear over `stalkRingEquiv`: the `O_{Y,f x}`-algebra
structure on `O_{X,x}` is by definition the `(f^{-1}O_Y)_x`-algebra structure precomposed
with `stalkRingEquiv`. -/
noncomputable def structureSemilinearEquiv :
    letI := (sharpStalk f OY OX alpha x).toAlgebra
    letI := (stalkHomOfSheaves (invRing f OY) OX alpha x).hom.toAlgebra
    ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u}) OX.obj x) ≃ₛₗ[stalkRingHom f OY x]
      ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u}) OX.obj x) :=
  letI := (sharpStalk f OY OX alpha x).toAlgebra
  letI := (stalkHomOfSheaves (invRing f OY) OX alpha x).hom.toAlgebra
  { AddEquiv.refl _ with
    map_smul' := fun r b => by
      simp only [AddEquiv.toFun_eq_coe, AddEquiv.refl_apply]
      rw [Algebra.smul_def, Algebra.smul_def, RingHom.algebraMap_toAlgebra,
        RingHom.algebraMap_toAlgebra, sharpStalk, RingHom.comp_apply] }

/-- The base-change comparison
`G_{f x} ⊗_{O_{Y,f x}} O_{X,x} ≃ (f⁻¹G)_x ⊗_{(f⁻¹O_Y)_x} O_{X,x}`, semilinear over
`stalkRingEquiv`. -/
noncomputable def tensorSemilinearEquiv :
    letI := (sharpStalk f OY OX alpha x).toAlgebra
    letI := (stalkHomOfSheaves (invRing f OY) OX alpha x).hom.toAlgebra
    TensorProduct (ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u}) OY.obj (f x)))
        (ToType (TopCat.Presheaf.stalk (C := Ab.{u}) (srcMod OY G).presheaf (f x)))
        (ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u}) OX.obj x)) ≃ₛₗ[stalkRingHom f OY x]
      TensorProduct (ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u}) (invRing f OY).obj x))
        (ToType (TopCat.Presheaf.stalk (C := Ab.{u}) (tgtMod f OY G).presheaf x))
        (ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u}) OX.obj x)) :=
  letI := (sharpStalk f OY OX alpha x).toAlgebra
  letI := (stalkHomOfSheaves (invRing f OY) OX alpha x).hom.toAlgebra
  TensorProduct.congr (stalkSemilinearEquiv f OY G x)
    (structureSemilinearEquiv f OY OX alpha x)

/-- `tensorSemilinearEquiv` on pure tensors. -/
theorem tensorSemilinearEquiv_tmul
    (m : ToType (TopCat.Presheaf.stalk (C := Ab.{u}) (srcMod OY G).presheaf (f x)))
    (b : ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u}) OX.obj x)) :
    letI := (sharpStalk f OY OX alpha x).toAlgebra
    letI := (stalkHomOfSheaves (invRing f OY) OX alpha x).hom.toAlgebra
    tensorSemilinearEquiv f OY G OX alpha x
        (m ⊗ₜ[ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u}) OY.obj (f x))] b)
      = stalkAddEquiv f OY G x m
        ⊗ₜ[ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u}) (invRing f OY).obj x)] b :=
  rfl

/-- The base-change comparison is `O_{X,x}`-linear for the right-factor actions. -/
theorem tensorSemilinearEquiv_smul
    (c : ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u}) OX.obj x)) :
    letI := (sharpStalk f OY OX alpha x).toAlgebra
    letI := (stalkHomOfSheaves (invRing f OY) OX alpha x).hom.toAlgebra
    letI := rightTensorModule (ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u}) OY.obj (f x)))
      (ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u}) OX.obj x))
      (ToType (TopCat.Presheaf.stalk (C := Ab.{u}) (srcMod OY G).presheaf (f x)))
    letI := rightTensorModule
      (ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u}) (invRing f OY).obj x))
      (ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u}) OX.obj x))
      (ToType (TopCat.Presheaf.stalk (C := Ab.{u}) (tgtMod f OY G).presheaf x))
    ∀ z, tensorSemilinearEquiv f OY G OX alpha x (c • z)
      = c • tensorSemilinearEquiv f OY G OX alpha x z := by
  let := (sharpStalk f OY OX alpha x).toAlgebra
  let := (stalkHomOfSheaves (invRing f OY) OX alpha x).hom.toAlgebra
  let := rightTensorModule (ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u}) OY.obj (f x)))
    (ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u}) OX.obj x))
    (ToType (TopCat.Presheaf.stalk (C := Ab.{u}) (srcMod OY G).presheaf (f x)))
  let := rightTensorModule
    (ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u}) (invRing f OY).obj x))
    (ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u}) OX.obj x))
    (ToType (TopCat.Presheaf.stalk (C := Ab.{u}) (tgtMod f OY G).presheaf x))
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul m b =>
      rw [rightTensorModule_smul_tmul, tensorSemilinearEquiv_tmul, tensorSemilinearEquiv_tmul,
        rightTensorModule_smul_tmul]
  | add z₁ z₂ h₁ h₂ => rw [smul_add, map_add, map_add, h₁, h₂, smul_add]

/-- The base-change comparison as an `O_{X,x}`-linear equivalence for the right-factor
actions. -/
noncomputable def tensorLinearEquiv :
    letI := (sharpStalk f OY OX alpha x).toAlgebra
    letI := (stalkHomOfSheaves (invRing f OY) OX alpha x).hom.toAlgebra
    letI := rightTensorModule (ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u}) OY.obj (f x)))
      (ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u}) OX.obj x))
      (ToType (TopCat.Presheaf.stalk (C := Ab.{u}) (srcMod OY G).presheaf (f x)))
    letI := rightTensorModule
      (ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u}) (invRing f OY).obj x))
      (ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u}) OX.obj x))
      (ToType (TopCat.Presheaf.stalk (C := Ab.{u}) (tgtMod f OY G).presheaf x))
    TensorProduct (ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u}) OY.obj (f x)))
        (ToType (TopCat.Presheaf.stalk (C := Ab.{u}) (srcMod OY G).presheaf (f x)))
        (ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u}) OX.obj x))
      ≃ₗ[ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u}) OX.obj x)]
      TensorProduct (ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u}) (invRing f OY).obj x))
        (ToType (TopCat.Presheaf.stalk (C := Ab.{u}) (tgtMod f OY G).presheaf x))
        (ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u}) OX.obj x)) := by
  letI := (sharpStalk f OY OX alpha x).toAlgebra
  letI := (stalkHomOfSheaves (invRing f OY) OX alpha x).hom.toAlgebra
  letI := rightTensorModule (ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u}) OY.obj (f x)))
    (ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u}) OX.obj x))
    (ToType (TopCat.Presheaf.stalk (C := Ab.{u}) (srcMod OY G).presheaf (f x)))
  letI := rightTensorModule
    (ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u}) (invRing f OY).obj x))
    (ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u}) OX.obj x))
    (ToType (TopCat.Presheaf.stalk (C := Ab.{u}) (tgtMod f OY G).presheaf x))
  exact AddEquiv.toLinearEquiv (tensorSemilinearEquiv f OY G OX alpha x).toAddEquiv
    (fun c z => tensorSemilinearEquiv_smul f OY G OX alpha x c z)

/-- For a morphism of ringed spaces `(f, f^\sharp)` and a sheaf of `O_Y`-modules `G`, the stalk
of the pullback `f^*G = O_X ⊗_{f^{-1}O_Y} f^{-1}G` at `x` is `G_{f(x)} ⊗_{O_{Y,f(x)}} O_{X,x}`,
where the tensor product uses `f^\sharp_x : O_{Y,f(x)} → O_{X,x}`. -/
@[stacks 0098,
  ega "0 4.3.1" "stalk formula",
  ega "0 6.7.2" "special case",
  ega "I 9.1.12" "case Y = S"]
noncomputable def stalkPullbackTensorIso :
    letI := (sharpStalk f OY OX alpha x).toAlgebra
    letI := rightTensorModule (ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u}) OY.obj (f x)))
      (ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u}) OX.obj x))
      (ToType (TopCat.Presheaf.stalk (C := Ab.{u}) (srcMod OY G).presheaf (f x)))
    TensorProduct (ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u}) OY.obj (f x)))
        (ToType (TopCat.Presheaf.stalk (C := Ab.{u}) (srcMod OY G).presheaf (f x)))
        (ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u}) OX.obj x))
      ≃ₗ[ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u}) OX.obj x)]
      ToType (TopCat.Presheaf.stalk (C := Ab.{u})
        (tensorSheaf (invRing f OY) OX alpha (invMod f OY G)).val.presheaf x) :=
  letI := (sharpStalk f OY OX alpha x).toAlgebra
  letI := (stalkHomOfSheaves (invRing f OY) OX alpha x).hom.toAlgebra
  letI := rightTensorModule (ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u}) OY.obj (f x)))
    (ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u}) OX.obj x))
    (ToType (TopCat.Presheaf.stalk (C := Ab.{u}) (srcMod OY G).presheaf (f x)))
  letI := rightTensorModule
    (ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u}) (invRing f OY).obj x))
    (ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u}) OX.obj x))
    (ToType (TopCat.Presheaf.stalk (C := Ab.{u}) (tgtMod f OY G).presheaf x))
  (tensorLinearEquiv f OY G OX alpha x).trans
    (mainIso (invRing f OY) OX alpha (invMod f OY G) x)

/-- Existence form of Stacks Tag 0098: the stalk of `f^*G` at `x` is `O_{X,x}`-linearly
isomorphic to `G_{f(x)} ⊗_{O_{Y,f(x)}} O_{X,x}`. -/
theorem nonempty_stalkPullbackTensorIso :
    letI := (sharpStalk f OY OX alpha x).toAlgebra
    letI := rightTensorModule (ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u}) OY.obj (f x)))
      (ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u}) OX.obj x))
      (ToType (TopCat.Presheaf.stalk (C := Ab.{u}) (srcMod OY G).presheaf (f x)))
    Nonempty (TensorProduct (ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u}) OY.obj (f x)))
        (ToType (TopCat.Presheaf.stalk (C := Ab.{u}) (srcMod OY G).presheaf (f x)))
        (ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u}) OX.obj x))
      ≃ₗ[ToType (TopCat.Presheaf.stalk (C := CommRingCat.{u}) OX.obj x)]
      ToType (TopCat.Presheaf.stalk (C := Ab.{u})
        (tensorSheaf (invRing f OY) OX alpha (invMod f OY G)).val.presheaf x)) :=
  ⟨stalkPullbackTensorIso f OY G OX alpha x⟩

end Semilinear


end PullbackStalkTensor
