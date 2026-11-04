module

public import StacksFrontier.AlgebraicGeometry.InternalHomPairing
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.InternalHomVariance
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InternalHomVariance
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksCore.Tactic.StacksAttribute

/-!
# Internal Hom of sheaves of modules takes colimits in the first variable to limits

Let `O` be a sheaf of commutative rings on a site `(C, J)` and let `G` be a sheaf of
`O`-modules.  Internal Hom into `G`, as a functor of its *first* variable, carries colimits of
sheaves of modules to limits.  This is the sheaf half of
[Stacks, Tag 03EN](https://stacks.math.columbia.edu/tag/03EN) in the first variable, and it is
the half that `Stacks.PresheafOfModules.InternalHom.internalHomFunctor_preservesColimitsOfShape`
and `Stacks.PresheafOfModules.InternalHom.internalHomSecondFunctor_preservesLimits` do not
cover: those are the two presheaf halves, and
`Stacks.SheafOfModules.InternalHom.internalHomSecondFunctor_preservesLimits` is the sheaf half
in the *second* variable only.

This statement is proved a second time, over a ringed site at a single universe, as
`Stacks.SheafOfModules.InternalHom.internalHomFirstFunctor_preservesColimitsOfSize`.  The
version here is the one stated over an arbitrary site `(C, J)` with `C : Type u` and
`Category.{v} C`, hence at module universe `max u v` rather than at `u`; that generality is what
`Stacks.SheafOfModules.InternalHom.sheafInternalHomFunctor` below is indexed by, and it is why
the two coexist.

The presheaf statement does not transfer by a comparison with the forgetful functor, because
colimits of sheaves of modules are not computed on the underlying presheaves.  What does
transfer is the *symmetry* of the internal Hom pairing: a morphism `A ⟶ Hom(B, G)` is the same
thing as a morphism `B ⟶ Hom(A, G)`, both being an `O`-bilinear pairing of `A` and `B` into `G`,
and that bijection is natural in both arguments.  Read into the opposite category, internal Hom
against `G` is therefore left adjoint to its own left opposite, and a left adjoint preserves
colimits.

## Main definitions

* `Stacks.SheafOfModules.InternalHom.sheafInternalHomObj`: the internal Hom of two sheaves of
  modules, as a sheaf of modules.  Its underlying presheaf is Tag 03EM's `internalHom`, which is
  a sheaf because the target is.
* `Stacks.SheafOfModules.InternalHom.sheafInternalHomObjMapLeft`: precomposition in the first
  variable.  The name records the object it is about:
  `Stacks.SheafOfModules.InternalHom.sheafInternalHomMapLeft` is the same construction stated
  over `Stacks.SheafOfModules.InternalHom.siteSheafInternalHom`, whose sheaf of rings is spelled
  `Stacks.SheafOfModules.TensorColimits.underlyingRingSheaf` rather than
  `Stacks.SheafOfModules.Tensor.ringSheaf`.
  The two spellings of the sheaf of rings are reducibly equal, but the two internal-Hom objects
  are distinct constants, so the two maps have types that `rw` and instance search cannot
  identify and both are kept.
* `Stacks.SheafOfModules.InternalHom.sheafInternalHomFunctor`: internal Hom against a fixed
  target, as a covariant functor into the opposite category, so that "colimits go to limits" is
  literally preservation of colimits rather than an unnamed comparison map.

## Main results

* `Stacks.SheafOfModules.InternalHom.sheafInternalHomFunctor_preservesColimitsOfShape`: it
  preserves colimits of every shape.

## Implementation notes

The symmetry of the pairing is built at the level of presheaves of modules, where it is a
computation with the slice sites and needs no sheaf condition, and then transported to sheaves
by the fact that a morphism of sheaves of modules is a morphism of the underlying presheaves.
That presheaf-level construction is `StacksFrontier.AlgebraicGeometry.InternalHomPairing`, shared
with the single-universe proof of the same statement over a `RingedSite`; only the transport to
sheaves and the adjunction are here.  Everything is at module universe `max u v`, which is where
`Stacks.PresheafOfModules.InternalHom.internalHomMapLeft` is stated.

The ring universe `w` is free, as it is in the second-variable statement
`Stacks.SheafOfModules.InternalHom.internalHomSecondFunctor_preservesLimits`: internal Hom and
its transpose are computations with the slice sites, and neither reads the ring universe
against the universes of the site.  The module universe is `max u v`, the universe at which the
internal Hom of two sheaves of modules at that universe again lands: sections of
`internalHom O F G` over `U` are morphisms on the slice site `C/U`, which lives in
`Type (max u v)`, so the module universe of the internal Hom is `max u v` whatever the module
universe of `F` and `G`.

The `J.HasSheafCompose (forget₂ CommRingCat RingCat)` hypothesis is assumed rather than derived,
following `Stacks.SheafOfModules.InternalHom.internalHomSecondFunctor_preservesLimits`. It is no
restriction on the site: `Stacks.hasSheafCompose_forget₂_commRingCat` provides it for every
Grothendieck topology and every universe of sections, so the statement below is the source's
statement over an arbitrary site.

## References

* [Stacks Project, Tag 03EN](https://stacks.math.columbia.edu/tag/03EN)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 01CQ](https://stacks.math.columbia.edu/tag/01CQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.SheafOfModules.InternalHom

section Sheaf

universe v u w

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable (O : Sheaf J CommRingCat.{w})

/-- The internal Hom of two sheaves of modules, as a sheaf of modules: the internal Hom
presheaf of Tag 03EM, which is a sheaf because the target is. -/
@[sga "4 IV 12.1" "partial"]
public noncomputable def sheafInternalHomObj
    (F G : _root_.SheafOfModules.{max u v} (Tensor.ringSheaf O)) :
    _root_.SheafOfModules.{max u v} (Tensor.ringSheaf O) :=
  ⟨internalHom O.obj F.val G.val, internalHom_isSheaf O.obj F.val G.val G.isSheaf⟩

/-- Precomposition in the first variable of the internal Hom sheaf. -/
public noncomputable def sheafInternalHomObjMapLeft
    {F F' G : _root_.SheafOfModules.{max u v} (Tensor.ringSheaf O)} (f : F ⟶ F') :
    sheafInternalHomObj J O F' G ⟶ sheafInternalHomObj J O F G :=
  ⟨Stacks.PresheafOfModules.InternalHom.internalHomMapLeft O.obj f.val⟩

/-- Internal Hom against a fixed sheaf of modules `G`, as a covariant functor into the
opposite category, so that "colimits in the first variable go to limits" is literally
preservation of colimits. -/
@[sga "4 IV 12.2" "partial"]
public noncomputable def sheafInternalHomFunctor
    (G : _root_.SheafOfModules.{max u v} (Tensor.ringSheaf O)) :
    _root_.SheafOfModules.{max u v} (Tensor.ringSheaf O) ⥤
      (_root_.SheafOfModules.{max u v} (Tensor.ringSheaf O))ᵒᵖ where
  obj F := op (sheafInternalHomObj J O F G)
  map f := (sheafInternalHomObjMapLeft J O f).op
  map_id F := by
    apply Quiver.Hom.unop_inj
    apply _root_.SheafOfModules.hom_ext
    apply _root_.PresheafOfModules.hom_ext
    intro X
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro g
    rfl
  map_comp f g := by
    apply Quiver.Hom.unop_inj
    apply _root_.SheafOfModules.hom_ext
    apply _root_.PresheafOfModules.hom_ext
    intro X
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro h
    rfl

private noncomputable def sheafTranspose
    {A B G : _root_.SheafOfModules.{max u v} (Tensor.ringSheaf O)}
    (f : A ⟶ sheafInternalHomObj J O B G) : B ⟶ sheafInternalHomObj J O A G :=
  ⟨Stacks.PresheafOfModules.InternalHom.transposeHom O.obj f.val⟩

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
private lemma sheafTranspose_involutive
    {A B G : _root_.SheafOfModules.{max u v} (Tensor.ringSheaf O)}
    (f : A ⟶ sheafInternalHomObj J O B G) :
    sheafTranspose J O (sheafTranspose J O f) = f :=
  _root_.SheafOfModules.hom_ext
    (Stacks.PresheafOfModules.InternalHom.transposeHom_involutive O.obj f.val)

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
private lemma sheafTranspose_comp
    {A A' B G : _root_.SheafOfModules.{max u v} (Tensor.ringSheaf O)}
    (f : A' ⟶ A) (g : A ⟶ sheafInternalHomObj J O B G) :
    sheafTranspose J O (f ≫ g) =
      sheafTranspose J O g ≫ sheafInternalHomObjMapLeft J O f := by
  refine _root_.SheafOfModules.hom_ext ?_
  ext U b
  refine _root_.PresheafOfModules.hom_ext fun V => ?_
  ext a
  rfl

/-- The symmetry of the internal Hom pairing, as an adjunction: internal Hom against `G`,
read into the opposite category, is left adjoint to its own left opposite. -/
private noncomputable def sheafInternalHomFirstAdjunction
    (G : _root_.SheafOfModules.{max u v} (Tensor.ringSheaf O)) :
    sheafInternalHomFunctor J O G ⊣ (sheafInternalHomFunctor J O G).leftOp :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ =>
        { toFun := fun f => sheafTranspose J O f.unop
          invFun := fun f => (sheafTranspose J O f).op
          left_inv := fun f => Quiver.Hom.unop_inj (sheafTranspose_involutive J O f.unop)
          right_inv := sheafTranspose_involutive J O }
      homEquiv_naturality_left_symm := fun f g =>
        Quiver.Hom.unop_inj (sheafTranspose_comp J O f g)
      homEquiv_naturality_right := fun f g => sheafTranspose_comp J O g.unop f.unop }

/-- **Stacks 03EN, sheaf case, first variable.** For a fixed target `G`, the internal Hom of
sheaves of modules takes colimits in the first variable to limits. -/
@[stacks 03EN "sheaf_first_variable", sga "4 IV 12.2" "partial, special case"]
public noncomputable instance sheafInternalHomFunctor_preservesColimitsOfShape
    (G : _root_.SheafOfModules.{max u v} (Tensor.ringSheaf O))
    (I : Type*) [Category I] :
    PreservesColimitsOfShape I (sheafInternalHomFunctor J O G) := by
  have := (sheafInternalHomFirstAdjunction J O G).leftAdjoint_preservesColimits
  infer_instance

end Sheaf

end Stacks.SheafOfModules.InternalHom

end
