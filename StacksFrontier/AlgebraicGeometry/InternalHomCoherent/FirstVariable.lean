module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHom
public import StacksFrontier.AlgebraicGeometry.InternalHomPairing
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.InternalHomVariance
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
import StacksCore.Tactic.StacksAttribute

/-!
# Internal Hom of sheaves of modules and colimits in the first variable

Let `(C, 𝒪)` be a ringed site and let `G` be a sheaf of `𝒪`-modules. The internal Hom
`SheafHom(F, G)` of `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHom` is contravariant
in `F`, and Stacks 03EN asserts that in that variable it carries arbitrary colimits to limits.
This file proves that for sheaves of modules; the two presheaf halves and the sheaf half in the
second variable are in `StacksFrontier.Algebra.Category.ModuleCat.Presheaf.InternalHomVariance` and
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InternalHomVariance`.

The proof is not the presheaf statement transported along the forgetful functor — that functor
does not preserve colimits — but the observation that the contravariant functor
`F ↦ SheafHom(F, G)`, read as a functor into the opposite category, is **left adjoint to its own
opposite**. A morphism `A ⟶ SheafHom(B, G)` is the same thing as a pairing `A × B ⟶ G`, bilinear
and natural over every object of the site, and that description is symmetric in `A` and `B`; the
resulting involution `transposeHom` is the unit and counit of the adjunction at once. A left
adjoint preserves all colimits, which is the assertion.

## Main definitions

* `Stacks.SheafOfModules.InternalHom.sheafInternalHom`: the internal Hom of two sheaves of
  modules on a ringed site, indexed by the ringed site's own sheaf of rings. See the
  implementation notes for why this spelling is needed.
* `Stacks.SheafOfModules.InternalHom.internalHomMapLeft`: precomposition in the first variable,
  `SheafHom(F', G) ⟶ SheafHom(F, G)` for `f : F ⟶ F'`.
* `Stacks.SheafOfModules.InternalHom.internalHomFirstFunctor`: internal Hom against a fixed
  target, as a functor into the opposite category of sheaves of modules, so that "colimits go to
  limits" is literally preservation of colimits.

## Main results

* `Stacks.SheafOfModules.InternalHom.internalHomFirstFunctor_preservesColimitsOfSize`:
  **Stacks 03EN, sheaf case, first variable.** Internal Hom against a fixed sheaf of modules
  carries colimits of every shape to limits.

## Implementation notes

The pairing attached to `f : A ⟶ SheafHom(B, G)` and its transpose live at the level of
presheaves of modules, since neither the sheaf condition nor sheafification plays any part; only
the final assembly is about sheaves. They are
`Stacks.PresheafOfModules.InternalHom.pairing`,
`Stacks.PresheafOfModules.InternalHom.transposeSection`,
`Stacks.PresheafOfModules.InternalHom.transposeHom` and
`Stacks.PresheafOfModules.InternalHom.transposeHom_involutive` of
`StacksFrontier.AlgebraicGeometry.InternalHomPairing`, shared with the arbitrary-site proof of the
same statement in `StacksFrontier.AlgebraicGeometry.InternalHomSiteVariance.FirstVariable`; they
are stated there at `Category.{v} C` and `CommRingCat.{max u v}`, which specialize to the
single-universe case used here.

Everything is stated at a single universe `u`: a `RingedSite.{u, u, u}` with
`SheafOfModules.{u}`. This is forced rather than chosen, since the internal Hom of two
`SheafOfModules.{w}` on a `RingedSite.{u, v, w}` is a `SheafOfModules.{max u v w}`, so internal
Hom is an endofunctor only in the equi-universe case. On the site of opens of a space
`X : Type u` the hom universe is `u` as well.

No `@[stacks 03EN]` attribute is placed here. Tag 03EN has four halves — first and second
variable, for presheaves and for sheaves — and each is carried by the declaration that states it:
`Stacks.PresheafOfModules.InternalHom.internalHomFunctor_preservesColimitsOfShape` and
`internalHomSecondFunctor_preservesLimits` in
`StacksFrontier.Algebra.Category.ModuleCat.Presheaf.InternalHomVariance`,
`Stacks.SheafOfModules.InternalHom.internalHomSecondFunctor_preservesLimits` in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InternalHomVariance`, and
`sheafInternalHomFunctor_preservesColimitsOfShape` in
`StacksFrontier.AlgebraicGeometry.InternalHomSiteVariance.FirstVariable`.

## References

* [Stacks Project, Tag 03EN](https://stacks.math.columbia.edu/tag/03EN)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace Stacks.SheafOfModules.InternalHom

universe w w' u

/-! ### Internal Hom against a fixed sheaf of modules, as a functor to the opposite category -/

section Sheaf

variable (X : RingedSite.{u, u, u})

/-- **The internal Hom of two sheaves of modules on a ringed site**, `SheafHom(F, G)`: the
internal-Hom presheaf of [Stacks, Tag 03EM], which is a sheaf since `G` is. It is
`Stacks.SheafOfModules.sheafHom` over the sheaf of rings `AlgebraicGeometry.RingedSite.ringSheaf`
of the ringed site; see `sheafInternalHom_eq_sheafHom`. -/
noncomputable abbrev sheafInternalHom
    (F G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) where
  val := internalHom X.O.obj F.val G.val
  isSheaf := internalHom_isSheaf X.O.obj F.val G.val G.isSheaf

/-- The internal Hom `sheafInternalHom X F G` is `Stacks.SheafOfModules.sheafHom` of `F` and
`G`. -/
lemma sheafInternalHom_eq_sheafHom
    (F G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    sheafInternalHom X F G =
      sheafHom X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property F G := rfl

/-- **Precomposition in the first variable of the internal Hom of sheaves of modules.** A
morphism `f : F ⟶ F'` induces `SheafHom(F', G) ⟶ SheafHom(F, G)`. -/
noncomputable def internalHomMapLeft
    {F F' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (f : F ⟶ F') :
    sheafInternalHom X F' G ⟶ sheafInternalHom X F G :=
  ⟨Stacks.PresheafOfModules.InternalHom.internalHomMapLeft X.O.obj f.val⟩

/-- **Internal Hom against a fixed sheaf of modules**, as a functor into the opposite category of
sheaves of modules, sending `F` to `SheafHom(F, G)` and `f : F ⟶ F'` to precomposition with `f`.
-/
noncomputable def internalHomFirstFunctor
    (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⥤
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))ᵒᵖ where
  obj F := op (sheafInternalHom X F G)
  map f := (internalHomMapLeft X G f).op
  map_id F := by
    apply Quiver.Hom.unop_inj
    apply _root_.SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro g
    rfl
  map_comp f g := by
    apply Quiver.Hom.unop_inj
    apply _root_.SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro h
    rfl

/-- The functor `internalHomFirstFunctor X G` sends `F` to `SheafHom(F, G)`, viewed in the
opposite category. -/
@[simp]
lemma internalHomFirstFunctor_obj
    (G F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (internalHomFirstFunctor X G).obj F = op (sheafInternalHom X F G) :=
  rfl

/-- The transpose of a morphism of sheaves of modules into an internal Hom. -/
private noncomputable def sheafTranspose
    {A B G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (f : A ⟶ sheafInternalHom X B G) : B ⟶ sheafInternalHom X A G :=
  ⟨Stacks.PresheafOfModules.InternalHom.transposeHom X.O.obj f.val⟩

private lemma sheafTranspose_involutive
    {A B G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (f : A ⟶ sheafInternalHom X B G) :
    sheafTranspose X (sheafTranspose X f) = f :=
  _root_.SheafOfModules.hom_ext
    (Stacks.PresheafOfModules.InternalHom.transposeHom_involutive X.O.obj f.val)

private lemma sheafTranspose_comp
    {A A' B G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (f : A' ⟶ A)
    (g : A ⟶ sheafInternalHom X B G) :
    sheafTranspose X (f ≫ g) = sheafTranspose X g ≫ internalHomMapLeft X G f := by
  ext U b
  refine PresheafOfModules.hom_ext fun V => ?_
  ext a
  rfl

/-- **Internal Hom against a fixed sheaf of modules is left adjoint to its own opposite.** The
unit and the counit are both the transpose involution: a morphism `A ⟶ SheafHom(B, G)` and a
morphism `B ⟶ SheafHom(A, G)` are the same datum, namely a natural bilinear pairing of `A` and
`B` into `G`. -/
private noncomputable def internalHomFirstAdjunction
    (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    internalHomFirstFunctor X G ⊣ (internalHomFirstFunctor X G).leftOp :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ =>
        { toFun := fun f => sheafTranspose X f.unop
          invFun := fun f => (sheafTranspose X f).op
          left_inv := fun f => Quiver.Hom.unop_inj (sheafTranspose_involutive X f.unop)
          right_inv := sheafTranspose_involutive X }
      homEquiv_naturality_left_symm := fun f g =>
        Quiver.Hom.unop_inj (sheafTranspose_comp X f g)
      homEquiv_naturality_right := fun f g => sheafTranspose_comp X g.unop f.unop }

/-- **Stacks 03EN, sheaf case, first variable.** Internal Hom against a fixed sheaf of modules
carries colimits of every shape in its first variable to limits: it is a left adjoint. -/
@[sga "4 IV 12.2" "partial, special case"]
noncomputable instance internalHomFirstFunctor_preservesColimitsOfSize
    (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    PreservesColimitsOfSize.{w, w'} (internalHomFirstFunctor X G) :=
  (internalHomFirstAdjunction X G).leftAdjoint_preservesColimits

end Sheaf

end Stacks.SheafOfModules.InternalHom

end
