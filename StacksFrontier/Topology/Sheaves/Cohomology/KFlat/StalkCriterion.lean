module

public import StacksFrontier.Topology.Sheaves.Modules.StalkKFlat
public import StacksFrontier.Topology.Sheaves.Modules.StalkTotalComplex
public import StacksFrontier.Topology.Sheaves.Modules.StalkTensorRing
public import StacksFrontier.Topology.Sheaves.Modules.Skyscraper
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.KFlatComplexesDefinition
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import StacksCore.Tactic.StacksAttribute

/-!
# The stalk criterion for K-flatness

Let `(X, O_X)` be a ringed space and `K` a complex of `O_X`-modules. Then `K` is K-flat
(Stacks 06YN: `Tot(F ⊗_{O_X} K)` is acyclic for every acyclic complex `F`) if and only if for
every `x : X` the complex `K_x` of `O_{X,x}`-modules is K-flat (Stacks 06XZ). That is
`kFlat_iff_stalkwise` below.

## The two directions

"Stalkwise K-flat implies K-flat" tests acyclicity of `Tot(F ⊗_{O_X} K)` at the stalks
(`acyclic_iff_forall_stalk_acyclic`, the module form of Stacks 01AG) and recognises the stalk of
that total complex as `Tot(F_x ⊗_{O_{X,x}} K_x)`.

"K-flat implies stalkwise K-flat" feeds an acyclic complex `M` of `O_{X,x}`-modules in as the
skyscraper `i_{x,*} M`, which is acyclic because `i_{x,*}` is exact, and then makes the same
identification, using that the stalk at `x` of `i_{x,*} M` is `M`.

So both directions rest on one statement: the stalk functor commutes with the total tensor
complex. That is `AlgebraicGeometry.SheafOfModules.stalkTotalComplexIso`, which is proved for an
arbitrary bifunctor and takes as an argument the comparison `ε` identifying the stalk of a value
of the bifunctor with the value at the stalks. For the tensor product that comparison had no
inhabitant, and supplying it is most of this file.

## Main definitions

* `Stacks.SheafOfModules.KFlatStalkCriterion.stalkTensorIso`: the comparison `ε` for the tensor
  product — Stacks 01CB in the
  spelling `AlgebraicGeometry.SheafOfModules.stalkFunctor` uses.
* `Stacks.SheafOfModules.KFlatStalkCriterion.stalkTensorComplexIso`: the stalk of the total tensor
  complex is the total
  tensor complex of the stalks.
* `Stacks.SheafOfModules.KFlatStalkCriterion.stalkComplexSkyscraperIso`: the stalk complex of a
  skyscraper complex.

## Main results

* `Stacks.SheafOfModules.KFlatStalkCriterion.kFlat_iff_stalkwise`: **Stacks 06YB.**
* `Stacks.SheafOfModules.KFlatStalkCriterion.stalkSMul_eq`: the two stalk-ring actions on a module
  stalk agree.
* `Stacks.SheafOfModules.KFlatStalkCriterion.stalkTensorIso_naturality_left`,
  `Stacks.SheafOfModules.KFlatStalkCriterion.stalkTensorIso_naturality_right`: `ε` is natural in
    each variable.

## Implementation notes

**Two rings, and why the comparison is work rather than a one-liner.** Stacks 01CB is proved in
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso` as a `≃ₗ` over the
  **`CommRingCat`**-valued stalk of the structure
sheaf, while `AlgebraicGeometry.SheafOfModules.stalkFunctor` takes its modules over the
**`RingCat`**-valued stalk of the same sheaf after forgetting commutativity. Those are isomorphic
rings, by `SemilinearStalk.commStalkRingEquiv`, but not equal ones, so a tensor product over one
is not a tensor product over the other. `stalkSMul_eq` says the two actions agree through that
isomorphism; `stalkSemilinearId` reads the identity on a module stalk as a semilinear equivalence
between them; and `stalkTensorRingEquiv` is `TensorProduct.congr` of two copies of it, Mathlib's
`congr` being already semilinear and already able to change the base ring. The two
`RingHomInvPair` instances it needs are seated here, `RingHomInvPair.of_ringEquiv` and
`of_ringEquiv_symm` being lemmas rather than instances in Mathlib.

**Two spellings of the ringed space, and why the file is in two halves.** Stacks 01CB is stated
over an `AlgebraicGeometry.RingedSpace`, while K-flatness is stated over a sheaf of commutative
rings on `Opens X` — the ringed-site form. The two are the same data, and
`AlgebraicGeometry.SheafOfModules.ringedSpaceOfSheaf` passes between them, but they are *not*
interchangeable to instance search: `JX` of a ringed space takes the carrier as a bare
topological space, so `Opens.grothendieckTopology ↑?X =?= Opens.grothendieckTopology Y.carrier`
asks for two different `TopologicalSpace` instances to agree, and nothing like
`(stalkFunctor _ x).Additive` is found at the ringed-space spelling. The comparison and its
naturality are therefore proved in the `RingedSpace` section, where Tag 01CB's module structures
are the ones instance search returns, and consumed in the `Site` section, where every argument
they are passed to is *explicit* — so the two spellings meet in a definitional check rather than
in instance search.

**The `Ring` instance on the stalk ring.** `ModuleCat` takes a `Ring` instance; for the stalk
ring instance search returns `RingCat`'s, whereas Mathlib's monoidal structure on `ModuleCat` is
keyed on the `Ring` derived from a `CommRing`. The two are definitionally equal but not
syntactically, so `MonoidalCategory (ModuleCat ↑(stalk ...))` is simply *not found* at the
spelling the stalk functor lands in — which is the spelling `stalkTotalComplexIso` states its
target bifunctor at, so the instance has to exist there. `monoidalStalkModuleCat` and
`monoidalPreadditiveStalkModuleCat` declare it at that spelling, with Mathlib's instances as
their bodies. Seating them anywhere else does not help: the `PreservesZeroMorphisms` hypotheses
of `stalkTotalComplexIso` mention the `HasZeroMorphisms` instances of the categories as *that
declaration* elaborated them, so an instance proved at the other spelling does not match the
goal even when it is in the local context.

## References

* [Stacks Project, Tag 01AG](https://stacks.math.columbia.edu/tag/01AG)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 06XZ](https://stacks.math.columbia.edu/tag/06XZ)
* [Stacks Project, Tag 06YB](https://stacks.math.columbia.edu/tag/06YB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace MonoidalCategory Opposite
open scoped TensorProduct

universe u

noncomputable section

namespace Stacks.SheafOfModules.KFlatStalkCriterion

section Space

variable (Y : AlgebraicGeometry.RingedSpace.{u, u}) (x : Y.carrier)

/-- The monoidal structure on presheaves of `O_Y`-modules, seated at the spelling
`(structureSheafRing Y).obj` of the presheaf of rings.

Only `[reducible]` definitions are unfolded when a goal is indexed into the discrimination tree
instance search looks in, and `structureSheafRing` is `[instance_reducible]`. So Mathlib's
`PresheafOfModules.monoidalCategoryStruct`, which is keyed on `R ⋙ forget₂ _ _`, is not
retrieved for a goal spelled `(structureSheafRing Y).obj`, even though the two are the same
functor. It is therefore declared here at that spelling, with Mathlib's instance as its body,
exactly as `monoidalStalkModuleCat` below is for the stalk ring. -/
instance monoidalCategoryStructPresheafOfModules :
    MonoidalCategoryStruct (PresheafOfModules.{u} (structureSheafRing Y).obj) :=
  inferInstanceAs (MonoidalCategoryStruct
    (PresheafOfModules.{u} (Y.presheaf ⋙ forget₂ CommRingCat RingCat)))

/-- The `CommRingCat`-valued stalk action of Tag 01CB agrees with the `RingCat`-valued one. -/
theorem stalkSMul_eq (M : PresheafOfModules.{u} (Stacks.SheafOfModules.TensorStalkRingedSpace.O Y))
    (s : TopCat.Presheaf.stalk (C := RingCat.{u}) (Stacks.SheafOfModules.TensorStalkRingedSpace.O Y)
      x)
    (m : Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk Y M x) :
    (SemilinearStalk.commStalkRingEquiv Y.presheaf x s) • m = s • m := by
  obtain ⟨U₁, hU₁, r₀, hr⟩ := TopCat.Presheaf.exists_germ_eq
    (Stacks.SheafOfModules.TensorStalkRingedSpace.O Y) s
  obtain ⟨U₂, hU₂, m₀, hm⟩ := TopCat.Presheaf.exists_germ_eq
    (C := AddCommGrpCat.{u}) M.presheaf m
  have hmem : x ∈ U₁ ⊓ U₂ := ⟨hU₁, hU₂⟩
  have hr' : TopCat.Presheaf.germ (C := RingCat.{u}) (Stacks.SheafOfModules.TensorStalkRingedSpace.O
    Y) (U₁ ⊓ U₂) x hmem
      ((Stacks.SheafOfModules.TensorStalkRingedSpace.O Y).map (homOfLE inf_le_left).op r₀) = s := by
    rw [TopCat.Presheaf.germ_res_apply (Stacks.SheafOfModules.TensorStalkRingedSpace.O Y)
      (homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁)) x hmem r₀]
    exact hr
  have hm' : TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) M.presheaf (U₁ ⊓ U₂) x hmem
      (M.presheaf.map (homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂)).op m₀) = m := by
    rw [TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{u}) M.presheaf
      (homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂)) x hmem m₀]
    exact hm
  rw [← hr', ← hm', SemilinearStalk.commStalkRingEquiv_germ]
  exact (Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule_germ_smul Y M x (U₁ ⊓ U₂) hmem
      ((Stacks.SheafOfModules.TensorStalkRingedSpace.O Y).map (homOfLE inf_le_left).op r₀)
      (M.presheaf.map (homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂)).op m₀)).symm.trans
    (PresheafOfModules.germ_ringCat_smul M x (U₁ ⊓ U₂) hmem
      ((Stacks.SheafOfModules.TensorStalkRingedSpace.O Y).map (homOfLE inf_le_left).op r₀)
      (M.presheaf.map (homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂)).op m₀))

/-- The `RingCat`-valued stalk ring to the `CommRingCat`-valued one. -/
def toCommStalkRing : ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
  (Stacks.SheafOfModules.TensorStalkRingedSpace.O Y) x) →+*
    ToType (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk Y x) :=
  (SemilinearStalk.commStalkRingEquiv Y.presheaf x).toRingHom

/-- The `CommRingCat`-valued stalk ring to the `RingCat`-valued one. -/
def ofCommStalkRing : ToType (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk Y x) →+*
    ToType (TopCat.Presheaf.stalk (C := RingCat.{u}) (Stacks.SheafOfModules.TensorStalkRingedSpace.O
      Y) x) :=
  (SemilinearStalk.commStalkRingEquiv Y.presheaf x).symm.toRingHom

/-- `toCommStalkRing` and `ofCommStalkRing` are mutually inverse ring homomorphisms. -/
instance ringHomInvPair_toCommStalkRing :
    RingHomInvPair (toCommStalkRing Y x) (ofCommStalkRing Y x) :=
  RingHomInvPair.of_ringEquiv (SemilinearStalk.commStalkRingEquiv Y.presheaf x)

/-- `ofCommStalkRing` and `toCommStalkRing` are mutually inverse ring homomorphisms. -/
instance ringHomInvPair_ofCommStalkRing :
    RingHomInvPair (ofCommStalkRing Y x) (toCommStalkRing Y x) :=
  RingHomInvPair.of_ringEquiv_symm (SemilinearStalk.commStalkRingEquiv Y.presheaf x)

/-- The identity on a module stalk, as a semilinear equivalence from the `CommRingCat`-stalk
module structure of Tag 01CB to the `RingCat`-stalk one, along `commStalkRingEquiv.symm`. -/
def stalkSemilinearId (M : PresheafOfModules.{u} (Stacks.SheafOfModules.TensorStalkRingedSpace.O Y))
  :
    ToType (Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk Y M x) ≃ₛₗ[ofCommStalkRing Y x]
      ToType (Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk Y M x) where
  toFun m := m
  map_add' _ _ := rfl
  map_smul' t m := by
    have h := stalkSMul_eq Y x M ((SemilinearStalk.commStalkRingEquiv Y.presheaf x).symm t) m
    rwa [RingEquiv.apply_symm_apply] at h
  invFun m := m
  left_inv _ := rfl
  right_inv _ := rfl

/-- The tensor product of two module stalks over the `CommRingCat`-valued stalk ring is the
tensor product over the `RingCat`-valued one, semilinearly. -/
def stalkTensorRingEquiv (M N : PresheafOfModules.{u}
  (Stacks.SheafOfModules.TensorStalkRingedSpace.O Y)) :
    (ToType (Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk Y M x) ⊗[ToType
      (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk Y x)]
        ToType (Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk Y N x)) ≃ₛₗ[ofCommStalkRing Y
          x]
      (ToType (Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk Y M x)
        ⊗[ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
          (Stacks.SheafOfModules.TensorStalkRingedSpace.O Y) x)]
          ToType (Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk Y N x)) :=
  TensorProduct.congr (stalkSemilinearId Y x M) (stalkSemilinearId Y x N)

/-- **Stacks 01CB in the `RingCat`-stalk spelling.** -/
def stalkTensorLinearEquiv (F G : SheafOfModules.{u}
  (structureSheafRing Y)) :
    letI := PresheafOfModules.instModuleCarrierStalkRingCatCarrierAbPresheafOpensCarrier
      (R := Stacks.SheafOfModules.TensorStalkRingedSpace.O Y)
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨Y.presheaf, Y.IsSheaf⟩).obj F).obj G).val x
    ToType (Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk Y
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨Y.presheaf, Y.IsSheaf⟩).obj F).obj G).val x)
      ≃ₗ[ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
        (Stacks.SheafOfModules.TensorStalkRingedSpace.O Y) x)]
      (ToType (Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk Y F.val x)
        ⊗[ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
          (Stacks.SheafOfModules.TensorStalkRingedSpace.O Y) x)]
          ToType (Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk Y G.val x)) := by
  letI := PresheafOfModules.instModuleCarrierStalkRingCatCarrierAbPresheafOpensCarrier
    (R := Stacks.SheafOfModules.TensorStalkRingedSpace.O Y)
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨Y.presheaf, Y.IsSheaf⟩).obj F).obj G).val x
  exact
    { toFun z := stalkTensorRingEquiv Y x F.val G.val
        (Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso Y x F G z)
      invFun w := (Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso Y x F G).symm
        ((stalkTensorRingEquiv Y x F.val G.val).symm w)
      map_add' a b :=
        (congrArg (fun t => stalkTensorRingEquiv Y x F.val G.val t)
          (map_add (Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso Y x F G) a b)).trans
          (map_add (stalkTensorRingEquiv Y x F.val G.val) _ _)
      map_smul' s z := by
        change stalkTensorRingEquiv Y x F.val G.val
            (Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso Y x F G (s • z)) =
          s • stalkTensorRingEquiv Y x F.val G.val
            (Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso Y x F G z)
        rw [← stalkSMul_eq Y x
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨Y.presheaf, Y.IsSheaf⟩).obj F).obj G).val s z]
        exact (congrArg (fun t => stalkTensorRingEquiv Y x F.val G.val t)
            ((Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso Y x F G).map_smulₛₗ
              (SemilinearStalk.commStalkRingEquiv Y.presheaf x s) z)).trans
          (((stalkTensorRingEquiv Y x F.val G.val).map_smulₛₗ
              (SemilinearStalk.commStalkRingEquiv Y.presheaf x s)
              (Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso Y x F G z)).trans
            (congrArg (fun r => r • stalkTensorRingEquiv Y x F.val G.val
                (Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso Y x F G z))
              ((SemilinearStalk.commStalkRingEquiv Y.presheaf x).symm_apply_apply s)))
      left_inv z :=
        (congrArg
          (fun t => (Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso Y x F G).symm t)
          ((stalkTensorRingEquiv Y x F.val G.val).symm_apply_apply
            (Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso Y x F G z))).trans
          ((Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso Y x F G).symm_apply_apply z)
      right_inv w :=
        (congrArg (fun t => stalkTensorRingEquiv Y x F.val G.val t)
          ((Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso Y x F G).apply_symm_apply
            ((stalkTensorRingEquiv Y x F.val G.val).symm w))).trans
          ((stalkTensorRingEquiv Y x F.val G.val).apply_symm_apply w)
    }

/-- **The comparison `ε` for the tensor product**, as a `ModuleCat` isomorphism. -/
def stalkTensorIso (F G : SheafOfModules.{u}
  (structureSheafRing Y)) :
    (AlgebraicGeometry.SheafOfModules.stalkFunctor
          (structureSheafRing Y) x).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨Y.presheaf, Y.IsSheaf⟩).obj F).obj G) ≅
      ((MonoidalCategory.curriedTensor (ModuleCat.{u}
            (TopCat.Presheaf.stalk (C := RingCat.{u})
              (Stacks.SheafOfModules.TensorStalkRingedSpace.O Y) x))).obj
          ((AlgebraicGeometry.SheafOfModules.stalkFunctor
            (structureSheafRing Y) x).obj F)).obj
        ((AlgebraicGeometry.SheafOfModules.stalkFunctor
          (structureSheafRing Y) x).obj G) :=
  LinearEquiv.toModuleIso (stalkTensorLinearEquiv Y x F G)

/-- The semilinear transport commutes with a tensor product of maps. -/
theorem stalkTensorRingEquiv_map (M M' N N' : PresheafOfModules.{u}
  (Stacks.SheafOfModules.TensorStalkRingedSpace.O Y))
    (a : ToType (Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk Y M x) →ₗ[ToType
      (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk Y x)]
      ToType (Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk Y M' x))
    (b : ToType (Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk Y N x) →ₗ[ToType
      (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk Y x)]
      ToType (Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk Y N' x))
    (a' : ToType (Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk Y M x)
        →ₗ[ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
          (Stacks.SheafOfModules.TensorStalkRingedSpace.O Y) x)]
      ToType (Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk Y M' x))
    (b' : ToType (Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk Y N x)
        →ₗ[ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
          (Stacks.SheafOfModules.TensorStalkRingedSpace.O Y) x)]
      ToType (Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk Y N' x))
    (ha : ∀ m, a m = a' m) (hb : ∀ n, b n = b' n)
    (w : ToType (Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk Y M x) ⊗[ToType
      (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk Y x)]
      ToType (Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk Y N x)) :
    stalkTensorRingEquiv Y x M' N' (TensorProduct.map a b w) =
      TensorProduct.map a' b' (stalkTensorRingEquiv Y x M N w) := by
  induction w using TensorProduct.inductionOn with
  | tmul m n =>
      rw [TensorProduct.map_tmul]
      change a m ⊗ₜ b n = TensorProduct.map a' b' (m ⊗ₜ n)
      rw [TensorProduct.map_tmul, ha, hb]
  | add p q hp hq => rw [map_add, map_add, map_add, map_add, hp, hq]

section Bridge

variable {F F' G G' : SheafOfModules.{u}
  (structureSheafRing Y)}

/-- Tag 01CB's induced map on the tensor product, in the sheafification spelling of Tag 06YM. -/
theorem tensorSheafMap_eq (f : F ⟶ F') (g : G ⟶ G') :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨Y.presheaf, Y.IsSheaf⟩).map f).app G ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨Y.presheaf, Y.IsSheaf⟩).obj F').map g =
      (PresheafOfModules.sheafification
          (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf ⟨Y.presheaf, Y.IsSheaf⟩).obj)
          (R := Stacks.SheafOfModules.Tensor.ringSheaf ⟨Y.presheaf, Y.IsSheaf⟩)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf ⟨Y.presheaf, Y.IsSheaf⟩).obj)).map
        (PresheafOfModules.tensorHom f.val g.val) :=
  Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map ⟨Y.presheaf, Y.IsSheaf⟩ f g

/-- The map `f ⊗ 𝟙 G` on sheaf tensor products is the sheafification of the right whiskering
`f.val ▷ G.val` of presheaves of modules. -/
theorem sheafTensor_map_app_eq (f : F ⟶ F')
    (G : SheafOfModules.{u} (structureSheafRing Y)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨Y.presheaf, Y.IsSheaf⟩).map f).app G =
      (PresheafOfModules.sheafification
          (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf ⟨Y.presheaf, Y.IsSheaf⟩).obj)
          (R := Stacks.SheafOfModules.Tensor.ringSheaf ⟨Y.presheaf, Y.IsSheaf⟩)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf ⟨Y.presheaf, Y.IsSheaf⟩).obj)).map
        (MonoidalCategory.whiskerRight f.val G.val) := rfl

/-- The sheafification of the right whiskering `f.val ▷ G.val` equals the sheafification of the
tensor product of maps `f.val ⊗ 𝟙 G.val`. -/
theorem whiskerRight_eq (f : F ⟶ F')
    (G : SheafOfModules.{u} (structureSheafRing Y)) :
    (PresheafOfModules.sheafification
        (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf ⟨Y.presheaf, Y.IsSheaf⟩).obj)
        (R := Stacks.SheafOfModules.Tensor.ringSheaf ⟨Y.presheaf, Y.IsSheaf⟩)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf ⟨Y.presheaf, Y.IsSheaf⟩).obj)).map
        (MonoidalCategory.whiskerRight f.val G.val) =
      (PresheafOfModules.sheafification
          (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf ⟨Y.presheaf, Y.IsSheaf⟩).obj)
          (R := Stacks.SheafOfModules.Tensor.ringSheaf ⟨Y.presheaf, Y.IsSheaf⟩)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf ⟨Y.presheaf, Y.IsSheaf⟩).obj)).map
        (PresheafOfModules.tensorHom f.val
          (CategoryTheory.CategoryStruct.id G).val) := rfl

/-- The map `𝟙 F ⊗ g` on sheaf tensor products is the sheafification of the left whiskering
`F.val ◁ g.val` of presheaves of modules. -/
theorem sheafTensor_obj_map_eq (g : G ⟶ G')
    (F : SheafOfModules.{u} (structureSheafRing Y)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨Y.presheaf, Y.IsSheaf⟩).obj F).map g =
      (PresheafOfModules.sheafification
          (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf ⟨Y.presheaf, Y.IsSheaf⟩).obj)
          (R := Stacks.SheafOfModules.Tensor.ringSheaf ⟨Y.presheaf, Y.IsSheaf⟩)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf ⟨Y.presheaf, Y.IsSheaf⟩).obj)).map
        (MonoidalCategory.whiskerLeft F.val g.val) := rfl

/-- The sheafification of the left whiskering `F.val ◁ g.val` equals the sheafification of the
tensor product of maps `𝟙 F.val ⊗ g.val`. -/
theorem whiskerLeft_eq (g : G ⟶ G')
    (F : SheafOfModules.{u} (structureSheafRing Y)) :
    (PresheafOfModules.sheafification
        (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf ⟨Y.presheaf, Y.IsSheaf⟩).obj)
        (R := Stacks.SheafOfModules.Tensor.ringSheaf ⟨Y.presheaf, Y.IsSheaf⟩)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf ⟨Y.presheaf, Y.IsSheaf⟩).obj)).map
        (MonoidalCategory.whiskerLeft F.val g.val) =
      (PresheafOfModules.sheafification
          (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf ⟨Y.presheaf, Y.IsSheaf⟩).obj)
          (R := Stacks.SheafOfModules.Tensor.ringSheaf ⟨Y.presheaf, Y.IsSheaf⟩)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf ⟨Y.presheaf, Y.IsSheaf⟩).obj)).map
        (PresheafOfModules.tensorHom
          (CategoryTheory.CategoryStruct.id F).val g.val) := rfl

/-- The identity induces the identity on stalks. -/
theorem stalkMapL_id (G : SheafOfModules.{u}
  (structureSheafRing Y))
    (n : ToType (Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk Y G.val x)) :
    Stacks.SheafOfModules.TensorStalkRingedSpace.stalkMapL Y G.val G.val
      (CategoryTheory.CategoryStruct.id G).val x n = n := by
  change ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
    ((PresheafOfModules.toPresheaf (Stacks.SheafOfModules.TensorStalkRingedSpace.O Y)).map (𝟙
      G.val))).hom n = n
  simp
  rfl

/-- `ε` is natural with respect to a pair of maps, given the stalk maps of each. -/
private theorem stalkTensorIso_naturality_aux {G G' : SheafOfModules.{u} (structureSheafRing Y)}
    (f : F ⟶ F') (g : G ⟶ G')
    (a : ToType (Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk Y F.val x) →ₗ[ToType
      (TopCat.Presheaf.stalk (C := RingCat.{u})
        (Stacks.SheafOfModules.TensorStalkRingedSpace.O Y) x)]
      ToType (Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk Y F'.val x))
    (b : ToType (Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk Y G.val x)
      →ₗ[ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
        (Stacks.SheafOfModules.TensorStalkRingedSpace.O Y) x)]
      ToType (Stacks.SheafOfModules.TensorStalkRingedSpace.grpStalk Y G'.val x))
    (ha : ∀ m, Stacks.SheafOfModules.TensorStalkRingedSpace.stalkMapL Y F.val F'.val f.val x m =
      a m)
    (hb : ∀ n, Stacks.SheafOfModules.TensorStalkRingedSpace.stalkMapL Y G.val G'.val g.val x n =
      b n) :
    (AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing Y) x).map
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨Y.presheaf, Y.IsSheaf⟩).map f).app G ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨Y.presheaf, Y.IsSheaf⟩).obj F').map g) ≫ (stalkTensorIso Y x F' G').hom =
      (stalkTensorIso Y x F G).hom ≫ ModuleCat.ofHom (TensorProduct.map a b) := by
  refine ModuleCat.hom_ext (LinearMap.ext fun z => ?_)
  let := Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule Y
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨Y.presheaf, Y.IsSheaf⟩).obj F).obj
      G).val x
  have hz := LinearMap.congr_fun
    (Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso_natural Y x F G F' G' f g) z
  exact (congrArg (fun t => stalkTensorRingEquiv Y x F'.val G'.val t) hz.symm).trans
    (stalkTensorRingEquiv_map Y x F.val F'.val G.val G'.val _ _ a b (fun m => ha m) hb _)

/-- `ε` is natural in the left variable. -/
theorem stalkTensorIso_naturality_left (f : F ⟶ F')
    (G : SheafOfModules.{u} (structureSheafRing Y)) :
    (AlgebraicGeometry.SheafOfModules.stalkFunctor
            (structureSheafRing Y) x).map
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨Y.presheaf, Y.IsSheaf⟩).map f).app G) ≫
        (stalkTensorIso Y x F' G).hom =
      (stalkTensorIso Y x F G).hom ≫
        ((MonoidalCategory.curriedTensor (ModuleCat.{u}
            (TopCat.Presheaf.stalk (C := RingCat.{u})
              (Stacks.SheafOfModules.TensorStalkRingedSpace.O Y) x))).map
          ((AlgebraicGeometry.SheafOfModules.stalkFunctor
            (structureSheafRing Y) x).map f)).app
          ((AlgebraicGeometry.SheafOfModules.stalkFunctor
            (structureSheafRing Y) x).obj G) := by
  rw [sheafTensor_map_app_eq, whiskerRight_eq, ← tensorSheafMap_eq]
  exact stalkTensorIso_naturality_aux Y x f (CategoryTheory.CategoryStruct.id G) _ LinearMap.id
    (fun _ => rfl) (stalkMapL_id Y x G)

/-- `ε` is natural in the right variable. -/
theorem stalkTensorIso_naturality_right
    (F : SheafOfModules.{u} (structureSheafRing Y)) (g
      : G ⟶ G') :
    (AlgebraicGeometry.SheafOfModules.stalkFunctor
            (structureSheafRing Y) x).map
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨Y.presheaf, Y.IsSheaf⟩).obj F).map g) ≫
        (stalkTensorIso Y x F G').hom =
      (stalkTensorIso Y x F G).hom ≫
        ((MonoidalCategory.curriedTensor (ModuleCat.{u}
            (TopCat.Presheaf.stalk (C := RingCat.{u})
              (Stacks.SheafOfModules.TensorStalkRingedSpace.O Y) x))).obj
          ((AlgebraicGeometry.SheafOfModules.stalkFunctor
            (structureSheafRing Y) x).obj F)).map
          ((AlgebraicGeometry.SheafOfModules.stalkFunctor
            (structureSheafRing Y) x).map g) := by
  rw [sheafTensor_obj_map_eq, whiskerLeft_eq, ← tensorSheafMap_eq]
  exact stalkTensorIso_naturality_aux Y x (CategoryTheory.CategoryStruct.id F) g LinearMap.id _
    (stalkMapL_id Y x F) (fun _ => rfl)

end Bridge

end Space

section Site

variable {X : TopCat.{u}}
  (R : CategoryTheory.Sheaf.{u, u, u, u + 1} (Opens.grothendieckTopology X) CommRingCat.{u})
  (x : X)

open AlgebraicGeometry.SheafOfModules

/-- The monoidal structure on modules over the stalk ring, seated at the spelling the stalk
functor produces.

`ModuleCat` takes a `Ring` instance, and for the stalk ring instance search returns `RingCat`'s,
whereas Mathlib's monoidal structure is keyed on the `Ring` derived from a `CommRing`. The two
are definitionally equal but not syntactically, so the instance is not *found* at the spelling
`AlgebraicGeometry.SheafOfModules.stalkFunctor` lands in — and that is the spelling
`stalkTotalComplexIso` states its target bifunctor at, so the instance must exist there. It is
declared, not inferred; the body is Mathlib's instance, accepted by definitional unfolding. -/
instance monoidalStalkModuleCat :
    MonoidalCategory (ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u})
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R).obj x)) :=
  ModuleCat.monoidalCategory

/-- Tensoring over the stalk ring is additive in each variable, at the same spelling. Without
this the additivity of `⊗` — and with it the total complex — is not found either, since
Mathlib's instance is keyed on the `CommRing`-derived `Ring` as above. -/
instance monoidalPreadditiveStalkModuleCat :
    MonoidalPreadditive (ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u})
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R).obj x)) :=
  inferInstanceAs (MonoidalPreadditive (@ModuleCat.{u} _
    (@CommRing.toRing _ (StacksDraft.StalkTensor.commRing_stalk_ringSheaf R x))))

/-- **The stalk of the total tensor complex is the total tensor complex of the stalks.** -/
def stalkTensorComplexIso
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R))
      ℤ) :
    letI := fun (left : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R)) =>
      Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{u, u, u, u, u} R left
    letI : HomologicalComplex.HasMapBifunctor K L
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R) (ComplexShape.up ℤ) :=
      Stacks.SheafOfModules.Tensor.hasMapBifunctor_sheafTensor R K L
    stalkComplex R x
        (HomologicalComplex.mapBifunctor K L
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R) (ComplexShape.up ℤ)) ≅
      HomologicalComplex.mapBifunctor (stalkComplex R x K) (stalkComplex R x L)
        (MonoidalCategory.curriedTensor (ModuleCat.{u}
          (TopCat.Presheaf.stalk (C := RingCat.{u})
            (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R).obj x)))
        (ComplexShape.up ℤ) := by
  letI := fun (left : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R)) =>
    Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{u, u, u, u, u} R left
  letI : HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R) (ComplexShape.up ℤ) :=
    Stacks.SheafOfModules.Tensor.hasMapBifunctor_sheafTensor R K L
  exact stalkTotalComplexIso (X := X) (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R)
    (MonoidalCategory.curriedTensor (ModuleCat.{u}
      (TopCat.Presheaf.stalk (C := RingCat.{u})
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R).obj x)))
    (stalkTensorIso (ringedSpaceOfSheaf R) x)
    (fun f N => stalkTensorIso_naturality_left (ringedSpaceOfSheaf R) x f N)
    (fun M {_ _} g => stalkTensorIso_naturality_right (ringedSpaceOfSheaf R) x M g) K L

/-- The stalk at `x` of the skyscraper complex at `x` is the complex one started with. -/
def stalkComplexSkyscraperIso
    (Mc : CochainComplex (ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u})
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R).obj x)) ℤ) :
    letI := skyscraperFunctor_additive (X := X) (Stacks.SheafOfModules.Tensor.ringSheaf R) x
    stalkComplex R x ((Functor.mapHomologicalComplex
      (skyscraperFunctor (X := X) (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x)
      (ComplexShape.up ℤ)).obj Mc) ≅ Mc := by
  letI := skyscraperFunctor_additive (X := X) (Stacks.SheafOfModules.Tensor.ringSheaf R) x
  letI := stalkFunctor_additive (X := X) (Stacks.SheafOfModules.Tensor.ringSheaf R) x
  change ((stalkFunctor (X := X) (Stacks.SheafOfModules.Tensor.ringSheaf R) x).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj
      (((skyscraperFunctor (X := X)
          (Stacks.SheafOfModules.Tensor.ringSheaf R) x).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj Mc) ≅ Mc
  exact (Functor.mapHomologicalComplexCompIso
    (skyscraperStalkIso (X := X) (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x)
    (ComplexShape.up ℤ)).app Mc ≪≫
      (Functor.mapHomologicalComplexIdIso _ (ComplexShape.up ℤ)).app Mc

/-- **Stacks 06YB.** A complex of sheaves of modules on a ringed space is K-flat if and only if
its complex of stalks at every point is K-flat over the stalk of the structure sheaf. -/
@[stacks 06YB]
theorem kFlat_iff_stalkwise
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)) ℤ)
      :
    letI := fun (left : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R)) =>
      Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{u, u, u, u, u} R left
    letI : ∀ (left right : CochainComplex
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ),
        HomologicalComplex.HasMapBifunctor left right
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R) (ComplexShape.up ℤ) :=
      fun left right => Stacks.SheafOfModules.Tensor.hasMapBifunctor_sheafTensor R left right
    Stacks.SheafOfModules.KFlat.{u, u, u} R K ↔ KFlatStalkwise R K := by
  let := fun (left : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R)) =>
    Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{u, u, u, u, u} R left
  let : ∀ (left right : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ),
      HomologicalComplex.HasMapBifunctor left right
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R) (ComplexShape.up ℤ) :=
    fun left right => Stacks.SheafOfModules.Tensor.hasMapBifunctor_sheafTensor R left right
  constructor
  · intro h x' Mc hMc
    have := skyscraperFunctor_additive (X := X) (Stacks.SheafOfModules.Tensor.ringSheaf R) x'
    have := skyscraperFunctor_preservesFiniteLimits (X := X)
      (Stacks.SheafOfModules.Tensor.ringSheaf R) x'
    have := skyscraperFunctor_preservesFiniteColimits (X := X)
      (Stacks.SheafOfModules.Tensor.ringSheaf R) x'
    have hG : ((Functor.mapHomologicalComplex
        (skyscraperFunctor (X := X) (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x')
        (ComplexShape.up ℤ)).obj Mc).Acyclic :=
      HomologicalComplex.Acyclic.map _ hMc
    have h2 := (acyclic_iff_forall_stalk_acyclic
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) _).1 (h _ hG) x'
    have h3 := HomologicalComplex.Acyclic.of_iso
      (stalkTensorComplexIso R x' ((Functor.mapHomologicalComplex
        (skyscraperFunctor (X := X) (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x')
        (ComplexShape.up ℤ)).obj Mc) K) h2
    exact HomologicalComplex.Acyclic.of_iso
      ((((MonoidalCategory.curriedTensor (ModuleCat.{u} (TopCat.Presheaf.stalk
          (C := RingCat.{u}) (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R).obj
            x'))).map₂HomologicalComplex
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)).mapIso
          (stalkComplexSkyscraperIso R x' Mc)).app (stalkComplex R x' K)) h3
  · intro h F hF
    rw [acyclic_iff_forall_stalk_acyclic (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)]
    intro x'
    exact HomologicalComplex.Acyclic.of_iso (stalkTensorComplexIso R x' F K).symm
      (h x' (stalkComplex R x' F)
        ((acyclic_iff_forall_stalk_acyclic (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) F).1
          hF x'))

end Site

end Stacks.SheafOfModules.KFlatStalkCriterion

end

end
