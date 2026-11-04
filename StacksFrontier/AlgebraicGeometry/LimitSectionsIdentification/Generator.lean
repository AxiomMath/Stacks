module

public import StacksFrontier.AlgebraicGeometry.LimitSectionsIdentification.Sections
public import StacksFrontier.AlgebraicGeometry.LimitSectionsIdentification.Free

/-!
# The pullback-sections presheaf of a module trivialized at the terminal stage

Fix a commutative ring `A₀`, a quasi-coherent module `F` on `Spec A₀`, and a trivialization `e`
of the global sections of the inverse image of `F` to `Over.mk (Spec.map (𝟙 A₀))` — the terminal
object of the category of schemes over `Spec A₀` — by `A₀` itself.  This file identifies the
value of the presheaf of Tag 03DS at `Spec β` with `A'`, for every `β : A₀ ⟶ A'`, and the
presheaf map with the ring homomorphism.

The case used in the refutation of the statement of Tag 01Z0 is `F` the structure sheaf, which is `structSheaf`
with its trivialization `structSheafTrivialization`.

## Main definitions

* `Stacks.LimitSectionsIdentification.gen`: the canonical generator of `Γ((Spec β)^* F, ⊤)`,
  namely the image of a fixed global section at the terminal object.
* `Stacks.LimitSectionsIdentification.genHom`: the comparison `A' ⟶ Γ((Spec β)^* F, ⊤)` of
  abelian groups, `a ↦ a • gen β`.
* `Stacks.LimitSectionsIdentification.structSheaf`: the structure sheaf of `Spec A₀`, presented
  as the sheaf associated to `A₀` as a module over itself.
* `Stacks.LimitSectionsIdentification.structSheafTrivialization`: its trivialization at the
  terminal object, from `Scheme.Modules.pullbackId` and the unit of the tilde--sections adjunction.

## Main results

* `Stacks.LimitSectionsIdentification.bijective_genMap`: `Γ((Spec β)^* F, ⊤)` is a free
  `A'`-module of rank one on `gen β`.
* `Stacks.LimitSectionsIdentification.map_gen`: the presheaf map carries `gen` to `gen`.
* `Stacks.LimitSectionsIdentification.genHom_naturality`: the comparison is natural, the presheaf
  map corresponding to the ring homomorphism under it.

## Implementation notes

The module `F`, the structure morphism `b` of the terminal object, and the trivialization `e` are
all variables, with `b` constrained only by `hb : b = 𝟙 (Spec A₀)`; the structure sheaf and
`Spec.map (𝟙 A₀)` are substituted only at the end. This is not for generality.
`AlgebraicGeometry.Scheme.Modules.pullback` is defined as a
`CategoryTheory.Functor.leftAdjoint`, hence through `Classical.choice`. The two
spellings of the global sections — `Γ(M, ⊤)` in `AddCommGrpCat` and
`AlgebraicGeometry.moduleSpecΓFunctor.obj M` in `ModuleCat` — have the same carrier, but checking
that requires projecting `M.val`, and when `M` is an inverse image of a module whose own `val`
reduces, that projection unfolds the choice term. With `F` a variable the projection is stuck and
the check is immediate; with the structure sheaf written in directly, the same check runs past the
kernel's deterministic timeout.

The scalar action of `A'` on `Γ(M, ⊤)` is the one `AlgebraicGeometry.moduleSpecΓFunctor` carries,
and it is *not* found by instance synthesis at the type `Γ(M, ⊤)`, which is an object of
`AddCommGrpCat` and carries only the action of `Γ(Spec A', ⊤)`. The two agree through
`Scheme.ΓSpecIso`, which is `genHom_apply`.

## References

* [The Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [The Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.AlgebraicGeometry.AffineBaseChangeIso
open scoped ChangeOfRings

universe u

namespace Stacks.LimitSectionsIdentification

/-- `Scheme.ΓSpecIso` transports the scalars along a ring homomorphism. -/
theorem appTop_ΓSpecIso_inv {A A' : CommRingCat.{u}} (γ : A ⟶ A') (a : A) :
    (Spec.map γ).appTop ((Scheme.ΓSpecIso A).inv a) = (Scheme.ΓSpecIso A').inv (γ a) := by
  have h := congr($(Scheme.ΓSpecIso_inv_naturality γ).hom a)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
  exact h.symm

section Stage

variable {A₀ : CommRingCat.{u}} (F : (Spec A₀).Modules) [F.IsQuasicoherent]
  (b : Spec A₀ ⟶ Spec A₀) (hb : b = 𝟙 (Spec A₀))
  [((Scheme.Modules.pullback b).obj F).IsQuasicoherent]
  (e : ModuleCat.of A₀ ↑A₀ ≅ moduleSpecΓFunctor.obj ((Scheme.Modules.pullback b).obj F))
  {A' : CommRingCat.{u}} (β : A₀ ⟶ A') (p : Spec A' ⟶ Spec A₀) (hp : Spec.map β ≫ b = p)

include hb in
/-- **`Over.mk b` is terminal** in the category of schemes over `Spec A₀`. -/
def isTerminalOverMk : IsTerminal (Over.mk b) := by
  rw [hb]
  exact Over.mkIdTerminal

/-- The chosen global section at the terminal object: the image of `1` under the
trivialization. -/
def baseGen : Γ((Scheme.Modules.pullback b).obj F, ⊤) := e.hom (1 : A₀)

/-- The unique morphism from `Spec β` to the terminal object of the over-category. -/
def toBase : Over.mk p ⟶ Over.mk b := overHom b β p hp

/-- The `A₀`-linear map from `A₀` to the global sections of the inverse image along `Spec β`. -/
def unitMap : ModuleCat.of A₀ ↑A₀ ⟶ (ModuleCat.restrictScalars β.hom).obj
    (moduleSpecΓFunctor.obj ((Scheme.Modules.pullback p).obj F)) :=
  e.hom ≫ sectionsLinearMap F b β p hp

omit [F.IsQuasicoherent] in
/-- The transpose of `unitMap` along `β` is an isomorphism. -/
theorem isIso_transposeExtend_unitMap : IsIso (transposeExtend β (unitMap F b e β p hp)) :=
  isIso_transposeExtend_comp β e.hom _
    (isIso_transposeExtend_sectionsLinearMap F b β p hp)

/-- **The canonical generator** of the global sections of the inverse image along `Spec β`: the
image of `baseGen` under the presheaf map of the unique morphism to the terminal object. -/
def gen : Γ((Scheme.Modules.pullback p).obj F, ⊤) :=
  pullbackSectionsMap F (toBase b β p hp) (baseGen F b e)

omit [F.IsQuasicoherent] [((Scheme.Modules.pullback b).obj F).IsQuasicoherent] in
/-- `unitMap` sends `1` to the canonical generator `gen`. -/
theorem unitMap_one : unitMap F b e β p hp (1 : A₀) = gen F b e β p hp :=
  comp_sectionsLinearMap_apply F b β p hp e.hom (1 : A₀)

/-- The `A'`-linear comparison of `A'` with the global sections of the inverse image. -/
def genMap : ModuleCat.of A' ↑A' ⟶
    moduleSpecΓFunctor.obj ((Scheme.Modules.pullback p).obj F) :=
  spanOne (moduleSpecΓFunctor.obj ((Scheme.Modules.pullback p).obj F)) (gen F b e β p hp)

omit [F.IsQuasicoherent] in
/-- **The global sections of the inverse image along `Spec β` are a free `A'`-module of rank one,
on `gen`.** -/
theorem bijective_genMap : Function.Bijective (genMap F b e β p hp) :=
  bijective_spanOne_of_isIso_transposeExtend' β (unitMap F b e β p hp)
    (isIso_transposeExtend_unitMap F b e β p hp) (gen F b e β p hp) (unitMap_one F b e β p hp)

/-- The comparison, as a map of abelian groups. -/
def genHom : AddCommGrpCat.of ↑A' ⟶ Γ((Scheme.Modules.pullback p).obj F, ⊤) :=
  AddCommGrpCat.ofHom (genMap F b e β p hp).hom.toAddMonoidHom

omit [F.IsQuasicoherent] [((Scheme.Modules.pullback b).obj F).IsQuasicoherent] in
/-- `genHom` sends `a` to `a • gen`, where `a` acts through `Scheme.ΓSpecIso`. -/
theorem genHom_apply (a : A') :
    genHom F b e β p hp a = (Scheme.ΓSpecIso A').inv a • gen F b e β p hp := rfl

/-- `genHom` is an isomorphism of abelian groups. -/
instance isIso_genHom : IsIso (genHom F b e β p hp) :=
  (ConcreteCategory.isIso_iff_bijective (genHom F b e β p hp)).mpr (bijective_genMap F b e β p hp)

end Stage

section Transition

variable {A₀ : CommRingCat.{u}} (F : (Spec A₀).Modules) [F.IsQuasicoherent]
  (b : Spec A₀ ⟶ Spec A₀) (hb : b = 𝟙 (Spec A₀))
  [((Scheme.Modules.pullback b).obj F).IsQuasicoherent]
  (e : ModuleCat.of A₀ ↑A₀ ≅ moduleSpecΓFunctor.obj ((Scheme.Modules.pullback b).obj F))
  {A' A'' : CommRingCat.{u}} (β : A₀ ⟶ A') (p : Spec A' ⟶ Spec A₀) (hp : Spec.map β ≫ b = p)
  (γ : A' ⟶ A'') (β' : A₀ ⟶ A'') (p' : Spec A'' ⟶ Spec A₀) (hp' : Spec.map β' ≫ b = p')
  (hq : Spec.map γ ≫ p = p')

include hb in
omit [((Scheme.Modules.pullback b).obj F).IsQuasicoherent] in
/-- **The presheaf map carries the canonical generator to the canonical generator.**  This is
contravariant functoriality of `pullbackSectionsMap` together with the terminality of
`Over.mk b`: a transition followed by the unique morphism to the terminal object is the unique
morphism to the terminal object. -/
theorem map_gen :
    pullbackSectionsMap F (overHom p γ p' hq) (gen F b e β p hp) = gen F b e β' p' hp' := by
  have hterm : overHom p γ p' hq ≫ toBase b β p hp = toBase b β' p' hp' :=
    (isTerminalOverMk b hb).hom_ext _ _
  have hcomp := pullbackSectionsMap_comp F (overHom p γ p' hq) (toBase b β p hp)
  rw [hterm] at hcomp
  exact (ConcreteCategory.congr_hom hcomp (baseGen F b e)).symm

include hb in
omit [((Scheme.Modules.pullback b).obj F).IsQuasicoherent] in
/-- **Naturality of the comparison**: the presheaf map is semilinear and carries the generator to
the generator, so under the comparison it is the ring homomorphism. -/
theorem genHom_naturality (a : A') :
    pullbackSectionsMap F (X := Over.mk p') (Y := Over.mk p) (overHom p γ p' hq)
        (genHom F b e β p hp a) = genHom F b e β' p' hp' (γ a) := by
  rw [genHom_apply, genHom_apply, pullbackSectionsMap_smul,
    map_gen F b hb e β p hp γ β' p' hp' hq]
  congr 1
  exact appTop_ΓSpecIso_inv γ a

include hb in
omit [((Scheme.Modules.pullback b).obj F).IsQuasicoherent] in
/-- **Naturality of the comparison**, as an equation of maps of abelian groups. -/
theorem genHom_comp :
    genHom F b e β p hp ≫
        pullbackSectionsMap F (X := Over.mk p') (Y := Over.mk p) (overHom p γ p' hq)
      = AddCommGrpCat.ofHom γ.hom.toAddMonoidHom ≫ genHom F b e β' p' hp' := by
  ext a
  exact genHom_naturality F b hb e β p hp γ β' p' hp' hq a

end Transition

section StructureSheaf

variable (A₀ : CommRingCat.{u})

/-- The structure sheaf of `Spec A₀`, presented as the sheaf associated to `A₀` as a module over
itself.  Presented this way it is quasi-coherent by instance synthesis. -/
def structSheaf : (Spec A₀).Modules := tilde (ModuleCat.of A₀ ↑A₀)

/-- The structure sheaf `structSheaf A₀` is quasi-coherent. -/
instance : (structSheaf A₀).IsQuasicoherent := by
  dsimp only [structSheaf]; infer_instance

/-- The inverse image of `structSheaf A₀` along `Spec.map (𝟙 A₀)` is quasi-coherent. -/
instance : ((Scheme.Modules.pullback (Spec.map (𝟙 A₀))).obj (structSheaf A₀)).IsQuasicoherent :=
  inferInstance

/-- **The global sections of the structure sheaf at the terminal object are `A₀`.**  The inverse
image along `Spec.map (𝟙 A₀)` is the module itself, and the global sections of an associated
sheaf are the module. -/
def structSheafTrivialization : ModuleCat.of A₀ ↑A₀ ≅
    moduleSpecΓFunctor.obj ((Scheme.Modules.pullback (Spec.map (𝟙 A₀))).obj (structSheaf A₀)) :=
  tilde.toTildeΓNatIso.app (ModuleCat.of A₀ ↑A₀) ≪≫
    (moduleSpecΓFunctor.mapIso
      ((Scheme.Modules.pullbackCongr (Spec.map_id A₀)).app (structSheaf A₀) ≪≫
        (Scheme.Modules.pullbackId (Spec A₀)).app (structSheaf A₀))).symm

end StructureSheaf

end Stacks.LimitSectionsIdentification

end
