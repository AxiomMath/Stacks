module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedRelativeTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedBimodule
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedModuleAbelian

/-!
# The right action of the second algebra on a graded relative tensor product

Let `O` be a sheaf of commutative rings on a site, let `A` and `B` be sheaves of graded
`O`-algebras, let `M` be a right graded `A`-module and let `N` be a graded `(A, B)`-bimodule.
This file makes `M ⊗_A N` a right graded `B`-module: `b` acts on `x ⊗ y` by `x ⊗ (y b)`, which
respects the `A`-balancing because the two actions on `N` commute.

## Main definitions

* `Stacks.bilinHom` is the internal hom of two presheaves of modules: its sections over `U` are
  the families of maps on sections indexed by the morphisms out of `U`. A morphism into it is
  the datum of a bilinear map (`Stacks.toBilinHom`), and it is the object through which the
  universal properties of a coproduct and of a cokernel produce bilinear maps out of them.
* `SheafOfModules.GradedBimodule.toLeftGradedModule` is the left graded module underlying a
  graded bimodule.
* `SheafOfModules.RelativeTensor.actPre` is the right action of `B` on the presheaf-level
  relative tensor product, as a morphism into an internal hom, and
  `SheafOfModules.RelativeTensor.preGradedModule` assembles it into a presheaf-level right
  graded `B`-module.
* `SheafOfModules.RelativeTensor.gradedTensorRight` is **the right graded `B`-module `M ⊗_A N`**,
  with `gradedTensorRight_piece` identifying its pieces with
  `SheafOfModules.RelativeTensor.gradedTensor`.
* `SheafOfModules.RelativeTensor.BalancedRight` is a balanced bilinear family which is
  `B`-linear in its second variable, and `SheafOfModules.RelativeTensor.BalancedRight.descRight`
  is the homomorphism of right graded `B`-modules it descends to.

## Main results

* `SheafOfModules.RelativeTensor.gradedTensorRight_smul_tmul` computes the action on a local
  section `x ⊗ y`: it is `x ⊗ (y b)`.
* `SheafOfModules.RelativeTensor.BalancedRight.descRight` is the `B`-linear descent of a
  balanced bilinear family which is `B`-linear in the second variable: **the universal property
  of `M ⊗_A N` survives the right action.**

## Implementation notes

Degree `n` of `M ⊗_A N` is the sheafification of a cokernel of a coproduct of objectwise tensor
products, so none of its sections can be written down, and the action cannot be defined on them
directly. It is defined instead on the presheaf-level cokernel and transported along the
sheafification unit by `SheafOfModules.PreGradedModule.transfer`, which is where a bilinear map
into a sheaf not seeing a local bijection in its first variable is used.

On the presheaf-level cokernel the sections are still inaccessible: a cokernel of a coproduct
has no sectionwise description either. What is used instead is that both are colimits, so a
*morphism* out of them is given by their universal properties, and `Stacks.bilinHom` converts
the datum of a bilinear map on sections into such a morphism. Every law of the action is
therefore proved as an equality of two morphisms out of the cokernel, reduced by `cancel_epi`
and `CategoryTheory.Limits.Sigma.hom_ext` to pure tensors of sections, where it is the
corresponding law of the bimodule. The target degree of the action is carried as a parameter
`d` together with a proof `n + i = d` rather than being `n + i` on the nose: the two sides of
the associativity law then live in one and the same degree and the statement needs no
transport.

An internal hom of presheaves of modules has sections indexed by the morphisms of the site, so
it lives in the join of the module universe with the universes of the site: `Stacks.BilinHomPi`
is a `Type (max u v w w')`. Source and target of the action morphism must lie in one
`PresheafOfModules.{·}`, so the module universe `m` has to satisfy `m = max u v m` as a level,
and the general solution of that is `max u v z` with `z` free. The module universe is therefore
written `max u v z` here, which is every universe at least as large as the site's. The universe
`t` of the sheaf of rings is unrelated to it.

Three applications carry their universe levels explicitly — `actSummandHom.{t, v, u, z}` inside
`actSummand`, and `actSum.{t, v, u, z}` and `balanceMap_comp_actSum.{t, v, u, z}` inside
`actPre`. Without them the elaborator meets `max u v ?z =?= max u v z`, which it postpones
rather than solves, so `?z` is still a metavariable while the tactic blocks of `actSummand` run
— `simp` then makes no progress against `actSummandHom_apply` — and discharging the postponed
constraint costs `actPre` more than 400000 heartbeats. The name `z` matters for the same reason:
Lean sorts the arguments of a `max` level, so a universe whose name sorts after `u` and `v`
keeps `max u v` a prefix of the normal form, which the level unifier can match, while one
sorting before them — `m`, say — normalizes to `max (max m u) v` and leaves every such
constraint stuck.

The base is a sheaf of commutative rings, as for `SheafOfModules.RelativeTensor.gradedTensor`:
commutativity is what makes the internal hom a presheaf of modules.

## References

* [Stacks Project, Tag 0FR2](https://stacks.math.columbia.edu/tag/0FR2)
* [Stacks Project, Tag 0FR4](https://stacks.math.columbia.edu/tag/0FR4)
* [Stacks Project, Tag 0FR5](https://stacks.math.columbia.edu/tag/0FR5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe t w w' a m v u z

namespace Stacks

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{t}}

/-- Two scalars act commutingly on the sections of a presheaf of modules over a presheaf of
commutative rings. -/
theorem smul_comm_sections (M : PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat RingCat))
    {V : Cᵒᵖ} (r s : (O ⋙ forget₂ CommRingCat RingCat).obj V) (y : M.obj V) :
    r • s • y = s • r • y := by
  rw [smul_smul, smul_smul, mul_comm]

section Restr

variable {R : Cᵒᵖ ⥤ RingCat.{t}}

/-- Restriction along an identity morphism is the identity. -/
@[simp]
theorem restr_id (M : PresheafOfModules.{w} R) {U : Cᵒᵖ} (x : M.obj U) : restr M (𝟙 U) x = x := by
  change M.map (𝟙 U) x = x
  simp
  rfl

/-- Restricting along `f` and then along `g` is restricting along `f ≫ g`. -/
theorem restr_restr (M : PresheafOfModules.{w} R) {U V W : Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W)
    (x : M.obj U) : restr M g (restr M f x) = restr M (f ≫ g) x :=
  (M.map_comp_apply f g x).symm

/-- Applying `M.restrictₛₗ f` and then restricting along `g` is restricting along `f ≫ g`. -/
theorem restr_restrictₛₗ (M : PresheafOfModules.{w} R) {U V W : Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W)
    (x : M.obj U) : restr M g (M.restrictₛₗ f x) = restr M (f ≫ g) x :=
  (M.map_comp_apply f g x).symm

/-- Restriction is additive. -/
theorem restr_add (M : PresheafOfModules.{w} R) {U V : Cᵒᵖ} (f : U ⟶ V) (x x' : M.obj U) :
    restr M f (x + x') = restr M f x + restr M f x' :=
  map_add (ConcreteCategory.hom (M.map f)) x x'

/-- Restriction along `f` is semilinear over the ring map `R.map f`. -/
theorem restr_smul (M : PresheafOfModules.{w} R) {U V : Cᵒᵖ} (f : U ⟶ V) (r : R.obj U)
    (x : M.obj U) : restr M f (r • x) = R.map f r • restr M f x :=
  M.map_smul f r x

end Restr

variable {G : PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat RingCat)}
  {P P' : PresheafOfModules.{w'} (O ⋙ forget₂ CommRingCat RingCat)}

/-- Families of additive maps on sections `G.obj V →+ P.obj V`, one for every morphism
`U ⟶ V`. -/
abbrev BilinHomPi (G : PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat RingCat))
    (P : PresheafOfModules.{w'} (O ⋙ forget₂ CommRingCat RingCat)) (U : Cᵒᵖ) :
    Type (max u v w w') :=
  ∀ (V : Cᵒᵖ), (U ⟶ V) → (G.obj V →+ P.obj V)

/-- The families `BilinHomPi G P U` form a module over the sections of the base over `U`, a scalar
`r` acting on the component at `f : U ⟶ V` through its restriction along `f`. -/
noncomputable instance (U : Cᵒᵖ) :
    Module ((O ⋙ forget₂ CommRingCat RingCat).obj U) (BilinHomPi G P U) where
  smul r φ := fun V f => AddMonoidHom.mk'
    (fun y => (O ⋙ forget₂ CommRingCat RingCat).map f r • φ V f y)
    (fun y y' => by rw [map_add, smul_add])
  one_smul φ := by
    funext V f
    refine AddMonoidHom.ext fun y => ?_
    change (O ⋙ forget₂ CommRingCat RingCat).map f (1 : _) • φ V f y = φ V f y
    simp
  mul_smul r s φ := by
    funext V f
    refine AddMonoidHom.ext fun y => ?_
    change (O ⋙ forget₂ CommRingCat RingCat).map f (r * s) • φ V f y =
      (O ⋙ forget₂ CommRingCat RingCat).map f r •
        (O ⋙ forget₂ CommRingCat RingCat).map f s • φ V f y
    rw [map_mul, mul_smul]
  smul_zero r := by
    funext V f
    refine AddMonoidHom.ext fun y => ?_
    change (O ⋙ forget₂ CommRingCat RingCat).map f r • (0 : P.obj V) = 0
    rw [smul_zero]
  smul_add r φ ψ := by
    funext V f
    refine AddMonoidHom.ext fun y => ?_
    change (O ⋙ forget₂ CommRingCat RingCat).map f r • (φ V f y + ψ V f y) =
      (O ⋙ forget₂ CommRingCat RingCat).map f r • φ V f y +
        (O ⋙ forget₂ CommRingCat RingCat).map f r • ψ V f y
    rw [smul_add]
  add_smul r s φ := by
    funext V f
    refine AddMonoidHom.ext fun y => ?_
    change (O ⋙ forget₂ CommRingCat RingCat).map f (r + s) • φ V f y =
      (O ⋙ forget₂ CommRingCat RingCat).map f r • φ V f y +
        (O ⋙ forget₂ CommRingCat RingCat).map f s • φ V f y
    rw [map_add, add_smul]
  zero_smul φ := by
    funext V f
    refine AddMonoidHom.ext fun y => ?_
    change (O ⋙ forget₂ CommRingCat RingCat).map f (0 : _) • φ V f y = 0
    simp

/-- The sections over `U` of the internal hom of `G` and `P`: the families of maps on sections
which are linear over the base and commute with restriction. -/
def bilinHomSubmodule (G : PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat RingCat))
    (P : PresheafOfModules.{w'} (O ⋙ forget₂ CommRingCat RingCat)) (U : Cᵒᵖ) :
    Submodule ((O ⋙ forget₂ CommRingCat RingCat).obj U) (BilinHomPi G P U) where
  carrier := {φ | (∀ (V : Cᵒᵖ) (f : U ⟶ V) (r : (O ⋙ forget₂ CommRingCat RingCat).obj V)
      (y : G.obj V), φ V f (r • y) = r • φ V f y) ∧
    ∀ (V W : Cᵒᵖ) (f : U ⟶ V) (g : V ⟶ W) (y : G.obj V),
      P.map g (φ V f y) = φ W (f ≫ g) (G.map g y)}
  zero_mem' :=
    ⟨fun V f r y => by
      change (0 : P.obj V) = r • (0 : P.obj V)
      rw [smul_zero], fun V W f g y => by
      change P.map g (0 : P.obj V) = (0 : P.obj W)
      rw [map_zero]
      rfl⟩
  add_mem' {φ ψ} hφ hψ :=
    ⟨fun V f r y => by
      change φ V f (r • y) + ψ V f (r • y) = r • (φ V f y + ψ V f y)
      rw [hφ.1, hψ.1, smul_add], fun V W f g y => by
      change P.map g (φ V f y + ψ V f y) = φ W (f ≫ g) (G.map g y) + ψ W (f ≫ g) (G.map g y)
      rw [map_add, hφ.2, hψ.2]
      rfl⟩
  smul_mem' r φ hφ :=
    ⟨fun V f s y => by
      change (O ⋙ forget₂ CommRingCat RingCat).map f r • φ V f (s • y) =
        s • ((O ⋙ forget₂ CommRingCat RingCat).map f r • φ V f y)
      rw [hφ.1, smul_comm_sections], fun V W f g y => by
      change P.map g ((O ⋙ forget₂ CommRingCat RingCat).map f r • φ V f y) =
        (O ⋙ forget₂ CommRingCat RingCat).map (f ≫ g) r • φ W (f ≫ g) (G.map g y)
      rw [PresheafOfModules.map_smul, hφ.2]
      congr 1
      simp⟩

/-- **The internal hom of two presheaves of modules**: its sections over `U` are the families of
maps on sections `G.obj V →+ P.obj V`, indexed by the morphisms `U ⟶ V`, which are linear over
the base and commute with restriction. A morphism into it out of `F` is the same datum as a
bilinear map on sections out of `F` and `G`. -/
noncomputable def bilinHom (G : PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat RingCat))
    (P : PresheafOfModules.{w'} (O ⋙ forget₂ CommRingCat RingCat)) :
    PresheafOfModules.{max u v w w'} (O ⋙ forget₂ CommRingCat RingCat) where
  obj U := ModuleCat.of _ (bilinHomSubmodule G P U)
  map {U V} f := ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars ((O ⋙ forget₂ CommRingCat RingCat).map f).hom).obj
      (ModuleCat.of _ (bilinHomSubmodule G P V)))
    { toFun := fun φ => ⟨fun W g => φ.1 W (f ≫ g),
        ⟨fun W g r y => φ.2.1 W (f ≫ g) r y, fun W X g h y => by
          rw [φ.2.2 W X (f ≫ g) h y, Category.assoc]⟩⟩
      map_add' := fun φ ψ => rfl
      map_smul' := fun r φ => by
        refine Subtype.ext ?_
        funext W g
        refine AddMonoidHom.ext fun y => ?_
        change (O ⋙ forget₂ CommRingCat RingCat).map (f ≫ g) r • φ.1 W (f ≫ g) y =
          (O ⋙ forget₂ CommRingCat RingCat).map g
            ((O ⋙ forget₂ CommRingCat RingCat).map f r) • φ.1 W (f ≫ g) y
        congr 1
        simp }
  map_id U := by
    refine ModuleCat.hom_ext (LinearMap.ext fun φ => Subtype.ext ?_)
    funext W g
    refine AddMonoidHom.ext fun y => ?_
    change φ.1 W (𝟙 U ≫ g) y = φ.1 W g y
    rw [Category.id_comp]
  map_comp {U V W} f g := by
    refine ModuleCat.hom_ext (LinearMap.ext fun φ => Subtype.ext ?_)
    funext X h
    refine AddMonoidHom.ext fun y => ?_
    change φ.1 X ((f ≫ g) ≫ h) y = φ.1 X (f ≫ g ≫ h) y
    rw [Category.assoc]

/-- The component of a section of the internal hom at a morphism of the site. -/
def hApp {U : Cᵒᵖ} (φ : (bilinHom G P).obj U) {V : Cᵒᵖ} (f : U ⟶ V) : G.obj V →+ P.obj V :=
  φ.1 V f

/-- A section of the internal hom, from a compatible family of maps on sections. -/
def hMk {U : Cᵒᵖ} (φ : ∀ (V : Cᵒᵖ), (U ⟶ V) → (G.obj V →+ P.obj V))
    (hlin : ∀ (V : Cᵒᵖ) (f : U ⟶ V) (r : (O ⋙ forget₂ CommRingCat RingCat).obj V)
      (y : G.obj V), φ V f (r • y) = r • φ V f y)
    (hnat : ∀ (V W : Cᵒᵖ) (f : U ⟶ V) (g : V ⟶ W) (y : G.obj V),
      restr P g (φ V f y) = φ W (f ≫ g) (restr G g y)) :
    (bilinHom G P).obj U :=
  ⟨φ, hlin, hnat⟩

/-- The components of `hMk φ hlin hnat` are those of `φ`. -/
@[simp]
theorem hApp_hMk {U : Cᵒᵖ} (φ) (hlin) (hnat) {V : Cᵒᵖ} (f : U ⟶ V) (y : G.obj V) :
    hApp (P := P) (hMk φ hlin hnat) f y = φ V f y := rfl

/-- Each component of a section of the internal hom is linear over the base. -/
theorem hApp_smul_right {U : Cᵒᵖ} (φ : (bilinHom G P).obj U) {V : Cᵒᵖ} (f : U ⟶ V)
    (r : (O ⋙ forget₂ CommRingCat RingCat).obj V) (y : G.obj V) :
    hApp φ f (r • y) = r • hApp φ f y :=
  φ.2.1 V f r y

/-- The components of a section of the internal hom commute with restriction. -/
theorem hApp_naturality {U : Cᵒᵖ} (φ : (bilinHom G P).obj U) {V W : Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W)
    (y : G.obj V) : restr P g (hApp φ f y) = hApp φ (f ≫ g) (restr G g y) :=
  φ.2.2 V W f g y

/-- Two sections of the internal hom with the same components are equal. -/
theorem hApp_ext {U : Cᵒᵖ} {φ ψ : (bilinHom G P).obj U}
    (h : ∀ (V : Cᵒᵖ) (f : U ⟶ V) (y : G.obj V), hApp φ f y = hApp ψ f y) : φ = ψ := by
  refine Subtype.ext ?_
  funext V f
  exact AddMonoidHom.ext fun y => h V f y

/-- The components of the zero section of the internal hom vanish. -/
@[simp]
theorem hApp_zero {U V : Cᵒᵖ} (f : U ⟶ V) (y : G.obj V) :
    hApp (G := G) (P := P) (0 : (bilinHom G P).obj U) f y = 0 := rfl

/-- The components of a sum of sections of the internal hom are the sums of the components. -/
@[simp]
theorem hApp_add {U : Cᵒᵖ} (φ ψ : (bilinHom G P).obj U) {V : Cᵒᵖ} (f : U ⟶ V) (y : G.obj V) :
    hApp (φ + ψ) f y = hApp φ f y + hApp ψ f y := rfl

/-- The components of a difference of sections of the internal hom are the differences of the
components. -/
@[simp]
theorem hApp_sub {U : Cᵒᵖ} (φ ψ : (bilinHom G P).obj U) {V : Cᵒᵖ} (f : U ⟶ V) (y : G.obj V) :
    hApp (φ - ψ) f y = hApp φ f y - hApp ψ f y := rfl

/-- The component at `f` of `r • φ` is the component of `φ` multiplied by the restriction of `r`
along `f`. -/
@[simp]
theorem hApp_smul {U : Cᵒᵖ} (r : (O ⋙ forget₂ CommRingCat RingCat).obj U)
    (φ : (bilinHom G P).obj U) {V : Cᵒᵖ} (f : U ⟶ V) (y : G.obj V) :
    hApp (r • φ) f y = (O ⋙ forget₂ CommRingCat RingCat).map f r • hApp φ f y := rfl

/-- The component at `f` of the restriction of `φ` along `g` is the component of `φ` at `g ≫ f`. -/
@[simp]
theorem hApp_restr {U V : Cᵒᵖ} (g : U ⟶ V) (φ : (bilinHom G P).obj U) {W : Cᵒᵖ} (f : V ⟶ W)
    (y : G.obj W) : hApp (restr (bilinHom G P) g φ) f y = hApp φ (g ≫ f) y := rfl

/-- The component at `f` of `(bilinHom G P).restrictₛₗ g φ` is the component of `φ` at `g ≫ f`. -/
@[simp]
theorem hApp_restrictₛₗ {U V : Cᵒᵖ} (g : U ⟶ V) (φ : (bilinHom G P).obj U) {W : Cᵒᵖ}
    (f : V ⟶ W) (y : G.obj W) :
    hApp ((bilinHom G P).restrictₛₗ g φ) f y = hApp φ (g ≫ f) y := rfl

/-- The morphism into an internal hom attached to a bilinear map on sections. -/
noncomputable def ofBilinHom
    {F : PresheafOfModules.{max u v w w'} (O ⋙ forget₂ CommRingCat RingCat)}
    (β : BilinearMap F G P) : F ⟶ bilinHom G P where
  app U := ModuleCat.ofHom (Y := (bilinHom G P).obj U)
    { toFun := fun x => hMk (fun V f => β.app V (restr F f x))
        (fun V f r y => β.map_smul_right V r _ y)
        (fun V W f g y => by rw [β.restr_bil, restr_restr])
      map_add' := fun x x' => hApp_ext fun V f y => by
        change β.app V (restr F f (x + x')) y = β.app V (restr F f x) y + β.app V (restr F f x') y
        rw [restr_add, β.map_add_left]
      map_smul' := fun r x => hApp_ext fun V f y => by
        change β.app V (restr F f (r • x)) y =
          (O ⋙ forget₂ CommRingCat RingCat).map f r • β.app V (restr F f x) y
        rw [restr_smul, β.map_smul_left] }
  naturality {U V} g := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => hApp_ext fun W f y => ?_)
    change β.app W (restr F f (restr F g x)) y = β.app W (restr F (g ≫ f) x) y
    rw [restr_restr]

/-- The component at `f` of the image of `x` under `ofBilinHom β` is `β` applied to the restriction
of `x` along `f`. -/
@[simp]
theorem hApp_ofBilinHom
    {F : PresheafOfModules.{max u v w w'} (O ⋙ forget₂ CommRingCat RingCat)}
    (β : BilinearMap F G P) {U : Cᵒᵖ} (x : F.obj U) {V : Cᵒᵖ} (f : U ⟶ V) (y : G.obj V) :
    hApp (PresheafOfModules.Hom.app (ofBilinHom β) U x) f y = β.app V (restr F f x) y := rfl

/-- The bilinear map on sections attached to a morphism into an internal hom. -/
noncomputable def toBilinHom
    {F : PresheafOfModules.{max u v w w'} (O ⋙ forget₂ CommRingCat RingCat)}
    (φ : F ⟶ bilinHom G P) : BilinearMap F G P where
  app U := AddMonoidHom.mk'
    (fun x => AddMonoidHom.mk' (fun y => hApp (PresheafOfModules.Hom.app φ U x) (𝟙 U) y)
      (fun y y' => map_add _ y y'))
    (fun x x' => AddMonoidHom.ext fun y => by
      change hApp (PresheafOfModules.Hom.app φ U (x + x')) (𝟙 U) y =
        hApp (PresheafOfModules.Hom.app φ U x) (𝟙 U) y +
          hApp (PresheafOfModules.Hom.app φ U x') (𝟙 U) y
      rw [map_add (ConcreteCategory.hom (PresheafOfModules.Hom.app φ U)) x x', hApp_add])
  map_smul_left U r x y := by
    change hApp (PresheafOfModules.Hom.app φ U (r • x)) (𝟙 U) y =
      r • hApp (PresheafOfModules.Hom.app φ U x) (𝟙 U) y
    rw [map_smul (ConcreteCategory.hom (PresheafOfModules.Hom.app φ U)) r x, hApp_smul]
    congr 1
    simp
  map_smul_right U r x y := hApp_smul_right _ _ r y
  naturality {U V} f x y := by
    change restr P f (hApp (PresheafOfModules.Hom.app φ U x) (𝟙 U) y) =
      hApp (PresheafOfModules.Hom.app φ V (restr F f x)) (𝟙 V) (restr G f y)
    rw [hApp_naturality, restr_app φ f x, hApp_restr, Category.id_comp, Category.comp_id]

/-- The bilinear map `toBilinHom φ` sends `x` and `y` to the identity component of `φ x` at `y`. -/
@[simp]
theorem toBilinHom_app
    {F : PresheafOfModules.{max u v w w'} (O ⋙ forget₂ CommRingCat RingCat)}
    (φ : F ⟶ bilinHom G P) (U : Cᵒᵖ) (x : F.obj U) (y : G.obj U) :
    (toBilinHom φ).app U x y = hApp (PresheafOfModules.Hom.app φ U x) (𝟙 U) y := rfl

/-- The internal hom is covariant in its target. -/
noncomputable def bilinHomMap (G : PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat RingCat))
    (ψ : P ⟶ P') : bilinHom G P ⟶ bilinHom G P' where
  app U := ModuleCat.ofHom (X := (bilinHom G P).obj U) (Y := (bilinHom G P').obj U)
    { toFun := fun φ => hMk (fun V f => (ConcreteCategory.hom
        (PresheafOfModules.Hom.app ψ V)).toAddMonoidHom.comp (hApp φ f))
        (fun V f r y => by
          change PresheafOfModules.Hom.app ψ V (hApp φ f (r • y)) =
            r • PresheafOfModules.Hom.app ψ V (hApp φ f y)
          rw [hApp_smul_right]
          exact map_smul (ConcreteCategory.hom (PresheafOfModules.Hom.app ψ V)) r _)
        (fun V W f g y => by
          change restr P' g (PresheafOfModules.Hom.app ψ V (hApp φ f y)) =
            PresheafOfModules.Hom.app ψ W (hApp φ (f ≫ g) (restr G g y))
          rw [← hApp_naturality, ← restr_app ψ g])
      map_add' := fun φ φ' => by
        refine hApp_ext fun V f y => ?_
        change PresheafOfModules.Hom.app ψ V (hApp (φ + φ') f y) =
          PresheafOfModules.Hom.app ψ V (hApp φ f y) + PresheafOfModules.Hom.app ψ V (hApp φ' f y)
        rw [hApp_add, map_add]
      map_smul' := fun r φ => by
        refine hApp_ext fun V f y => ?_
        change PresheafOfModules.Hom.app ψ V (hApp (r • φ) f y) =
          (O ⋙ forget₂ CommRingCat RingCat).map f r •
            PresheafOfModules.Hom.app ψ V (hApp φ f y)
        rw [hApp_smul, map_smul] }
  naturality {U V} g := by
    refine ModuleCat.hom_ext (LinearMap.ext fun φ => hApp_ext fun W f y => ?_)
    rfl

/-- The components of the image of `φ` under `bilinHomMap G ψ` are those of `φ` followed by `ψ`. -/
@[simp]
theorem hApp_bilinHomMap (ψ : P ⟶ P') {U : Cᵒᵖ} (φ : (bilinHom G P).obj U) {V : Cᵒᵖ}
    (f : U ⟶ V) (y : G.obj V) :
    hApp (PresheafOfModules.Hom.app (bilinHomMap G ψ) U φ) f y =
      PresheafOfModules.Hom.app ψ V (hApp φ f y) := rfl

/-- The identity component of `r • φ` is `r` times the identity component of `φ`. -/
theorem hApp_smul_id {U : Cᵒᵖ} (r : (O ⋙ forget₂ CommRingCat RingCat).obj U)
    (φ : (bilinHom G P).obj U) (y : G.obj U) :
    hApp (r • φ) (𝟙 U) y = r • hApp φ (𝟙 U) y := by
  rw [hApp_smul]
  congr 1
  simp

/-- Evaluation of the internal hom at a global section of its source. -/
noncomputable def bilinHomEval (s : G.sections)
    (P : PresheafOfModules.{max u v w w'} (O ⋙ forget₂ CommRingCat RingCat)) :
    bilinHom G P ⟶ P where
  app U := ModuleCat.ofHom (X := (bilinHom G P).obj U)
    { toFun := fun φ => hApp φ (𝟙 U) (s.eval U)
      map_add' := fun φ ψ => hApp_add φ ψ (𝟙 U) (s.eval U)
      map_smul' := fun r φ => hApp_smul_id r φ (s.eval U) }
  naturality {U V} g := by
    refine ModuleCat.hom_ext (LinearMap.ext fun φ => ?_)
    change hApp φ (g ≫ 𝟙 V) (s.eval V) = restr P g (hApp φ (𝟙 U) (s.eval U))
    rw [hApp_naturality, Category.id_comp, Category.comp_id, restr_sections]

/-- Evaluation at `s` sends a section `φ` over `U` to its identity component applied to the
restriction of `s` to `U`. -/
@[simp]
theorem bilinHomEval_app (s : G.sections)
    (P : PresheafOfModules.{max u v w w'} (O ⋙ forget₂ CommRingCat RingCat)) (U : Cᵒᵖ)
    (φ : (bilinHom G P).obj U) :
    PresheafOfModules.Hom.app (bilinHomEval s P) U φ = hApp φ (𝟙 U) (s.eval U) := rfl

variable {G' G'' : PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat RingCat)}

/-- Currying along a bilinear multiplication `G × G' ⟶ G''`: a map out of `G''` becomes a map
out of `G` whose values are maps out of `G'`. -/
noncomputable def bilinHomUncurry (μ : BilinearMap G G' G'')
    (P : PresheafOfModules.{w'} (O ⋙ forget₂ CommRingCat RingCat)) :
    bilinHom G'' P ⟶ bilinHom G (bilinHom G' P) where
  app U := ModuleCat.ofHom (X := (bilinHom G'' P).obj U)
    (Y := (bilinHom G (bilinHom G' P)).obj U)
    { toFun := fun φ => hMk
        (fun V f => AddMonoidHom.mk'
          (fun b => hMk
            (fun W g => AddMonoidHom.mk'
              (fun b' => hApp φ (f ≫ g) (μ.app W (restr G g b) b'))
              (fun b' b'' => by rw [map_add (μ.app W (restr G g b)), map_add]))
            (fun W g r b' => by
              change hApp φ (f ≫ g) (μ.app W (restr G g b) (r • b')) =
                r • hApp φ (f ≫ g) (μ.app W (restr G g b) b')
              rw [μ.map_smul_right, hApp_smul_right])
            (fun W W' g g' b' => by
              change restr P g' (hApp φ (f ≫ g) (μ.app W (restr G g b) b')) =
                hApp φ (f ≫ g ≫ g') (μ.app W' (restr G (g ≫ g') b) (restr G' g' b'))
              rw [hApp_naturality, μ.restr_bil, restr_restr, Category.assoc]))
          (fun b b' => hApp_ext fun W g b'' => by
            change hApp φ (f ≫ g) (μ.app W (restr G g (b + b')) b'') = _
            rw [restr_add, μ.map_add_left, map_add]
            rfl))
        (fun V f r b => hApp_ext fun W g b' => by
          rw [hApp_smul]
          change hApp φ (f ≫ g) (μ.app W (restr G g (r • b)) b') =
            (O ⋙ forget₂ CommRingCat RingCat).map g r •
              hApp φ (f ≫ g) (μ.app W (restr G g b) b')
          rw [restr_smul, μ.map_smul_left, hApp_smul_right])
        (fun V W f g b => hApp_ext fun W' g' b' => by
          change hApp φ (f ≫ g ≫ g') (μ.app W' (restr G (g ≫ g') b) b') =
            hApp φ ((f ≫ g) ≫ g') (μ.app W' (restr G g' (restr G g b)) b')
          rw [restr_restr, Category.assoc])
      map_add' := fun φ ψ => hApp_ext fun V f b => hApp_ext fun W g b' => by
        change hApp (φ + ψ) (f ≫ g) (μ.app W (restr G g b) b') = _
        rw [hApp_add]
        rfl
      map_smul' := fun r φ => hApp_ext fun V f b => hApp_ext fun W g b' => by
        change hApp (r • φ) (f ≫ g) (μ.app W (restr G g b) b') =
          (O ⋙ forget₂ CommRingCat RingCat).map g ((O ⋙ forget₂ CommRingCat RingCat).map f r) •
            hApp φ (f ≫ g) (μ.app W (restr G g b) b')
        rw [hApp_smul]
        congr 1
        simp }
  naturality {U V} g := by
    refine ModuleCat.hom_ext (LinearMap.ext fun φ => hApp_ext fun W f b => hApp_ext
      fun W' f' b' => ?_)
    change hApp φ (g ≫ f ≫ f') (μ.app W' (restr G f' b) b') =
      hApp φ ((g ≫ f) ≫ f') (μ.app W' (restr G f' b) b')
    rw [Category.assoc]

/-- The uncurried section sends `b` and `b'` to `φ` applied to their product `μ (b|_W) b'`. -/
@[simp]
theorem hApp_bilinHomUncurry (μ : BilinearMap G G' G'')
    (P : PresheafOfModules.{w'} (O ⋙ forget₂ CommRingCat RingCat)) {U : Cᵒᵖ}
    (φ : (bilinHom G'' P).obj U) {V : Cᵒᵖ} (f : U ⟶ V) (b : G.obj V) {W : Cᵒᵖ} (g : V ⟶ W)
    (b' : G'.obj W) :
    hApp (hApp (PresheafOfModules.Hom.app (bilinHomUncurry μ P) U φ) f b) g b' =
      hApp φ (f ≫ g) (μ.app W (restr G g b) b') := rfl

end Stacks

namespace SheafOfModules

section LeftOfBimodule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A B : GradedAlgebra.{t, a} R}

/-- The left graded `A`-module underlying a graded `(A, B)`-bimodule. -/
def GradedBimodule.toLeftGradedModule (N : GradedBimodule.{t, a, m} A B) :
    LeftGradedModule.{t, a, m} A where
  piece := N.piece
  smul i n U := (N.leftMul i n).app U
  smul_smul_left i n U r x y := (N.leftMul i n).map_smul_left U r x y
  smul_smul_right i n U r x y := (N.leftMul i n).map_smul_right U r x y
  smul_naturality i n _U _V f x y := (N.leftMul i n).naturality f x y
  mul_smul i j n U x y z := (N.left_assoc i j n U x y z).symm
  one_smul n U x := N.one_left n U x

/-- The pieces of the underlying left graded module are those of the bimodule. -/
@[simp]
theorem GradedBimodule.toLeftGradedModule_piece (N : GradedBimodule.{t, a, m} A B) (n : ℤ) :
    N.toLeftGradedModule.piece n = N.piece n := rfl

/-- The action of the underlying left graded module is the left action of the bimodule. -/
@[simp]
theorem GradedBimodule.toLeftGradedModule_smul (N : GradedBimodule.{t, a, m} A B) (i n : ℤ)
    (U : Cᵒᵖ) : N.toLeftGradedModule.smul i n U = (N.leftMul i n).app U := rfl

end LeftOfBimodule

namespace RelativeTensor

open Stacks CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] {Osharp : Sheaf J CommRingCat.{t}}
  {A B : GradedAlgebra.{t, max u v z} (toRingCat J Osharp)}
  (M : GradedModule.{t, max u v z, max u v z} A)
  (N : GradedBimodule.{t, max u v z, max u v z} A B)

/-- The index `(p, q + i)` of the summand containing `x ⊗ (y b)`, for `x ⊗ y` of index
`(p, q)`. -/
abbrev actIndex {n : ℤ} (p : TensorIndex n) (i d : ℤ) (h : n + i = d) : TensorIndex d :=
  ⟨(p.1.1, p.1.2 + i), by have hp := p.2; omega⟩

/-- The relation index `(r, s, t + i)` attached to a relation index `(r, s, t)` of degree `n`
and a degree `i`. -/
abbrev actRelIndex {n : ℤ} (j : RelationIndex n) (i d : ℤ) (h : n + i = d) : RelationIndex d :=
  ⟨(j.1.1, j.1.2.1, j.1.2.2 + i), by
    change j.1.1 + j.1.2.1 + (j.1.2.2 + i) = d
    have hj := j.2
    omega⟩

/-- The right `B`-action of the bimodule, read on the underlying left graded `A`-module. -/
noncomputable def rightMulL (q i : ℤ) :
    Stacks.BilinearMap (N.toLeftGradedModule.piece q).val (B.piece i).val
      (N.toLeftGradedModule.piece (q + i)).val :=
  N.rightMul q i

/-- `rightMulL N q i` is the right action `N.rightMul q i` on sections. -/
theorem rightMulL_app (q i : ℤ) (U : Cᵒᵖ) (y : (N.toLeftGradedModule.piece q).val.obj U)
    (b : (B.piece i).val.obj U) : (rightMulL N q i).app U y b = (N.rightMul q i).app U y b := rfl

/-- The right action of the bimodule commutes with restriction. -/
theorem rightMulL_restr (q i : ℤ) {U V : Cᵒᵖ} (f : U ⟶ V)
    (y : (N.toLeftGradedModule.piece q).val.obj U) (b : (B.piece i).val.obj U) :
    restr (N.toLeftGradedModule.piece (q + i)).val f ((rightMulL N q i).app U y b) =
      (rightMulL N q i).app V (restr (N.toLeftGradedModule.piece q).val f y)
        (restr (B.piece i).val f b) :=
  (rightMulL N q i).restr_bil f y b

/-- The left action of the underlying left graded module commutes with restriction. -/
theorem smulL_restr (q r : ℤ) {U V : Cᵒᵖ} (f : U ⟶ V) (aa : (A.piece q).val.obj U)
    (y : (N.toLeftGradedModule.piece r).val.obj U) :
    restr (N.toLeftGradedModule.piece (q + r)).val f (N.toLeftGradedModule.smul q r U aa y) =
      N.toLeftGradedModule.smul q r V (restr (A.piece q).val f aa)
        (restr (N.toLeftGradedModule.piece r).val f y) :=
  N.toLeftGradedModule.smul_naturality q r f aa y

/-- The right action of the right graded module commutes with restriction. -/
theorem smulR_restr (n i : ℤ) {U V : Cᵒᵖ} (f : U ⟶ V) (x : (M.piece n).val.obj U)
    (aa : (A.piece i).val.obj U) :
    restr (M.piece (n + i)).val f (M.smul n i U x aa) =
      M.smul n i V (restr (M.piece n).val f x) (restr (A.piece i).val f aa) :=
  M.smul_naturality n i f x aa

/-- The local section `x ⊗ y` of degree `n` of the presheaf-level relative tensor product, as a
bilinear map on sections. -/
noncomputable def tmulPreBil (n : ℤ) (p : TensorIndex n) :
    Stacks.BilinearMap (M.piece p.1.1).val (N.toLeftGradedModule.piece p.1.2).val
      (gradedTensorPre M N.toLeftGradedModule n) :=
  PresheafOfModules.toBilinear (tensorSumι M N.toLeftGradedModule p ≫
    gradedTensorπ M N.toLeftGradedModule n)

/-- The local section `x ⊗ y` of degree `n` of the presheaf-level relative tensor product. -/
noncomputable def tmulPre (n : ℤ) (p : TensorIndex n) (X : Cᵒᵖ)
    (x : (M.piece p.1.1).val.obj X) (y : (N.toLeftGradedModule.piece p.1.2).val.obj X) :
    (gradedTensorPre M N.toLeftGradedModule n).obj X :=
  (tmulPreBil M N n p).app X x y

/-- The pure tensor `x ⊗ y` is the image of `x ⊗ₜ y` in the summand of index `p` under the quotient
map of the presentation. -/
theorem tmulPre_eq (n : ℤ) (p : TensorIndex n) (X : Cᵒᵖ) (x : (M.piece p.1.1).val.obj X)
    (y : (N.toLeftGradedModule.piece p.1.2).val.obj X) :
    tmulPre M N n p X x y =
      PresheafOfModules.Hom.app (gradedTensorπ M N.toLeftGradedModule n) X
        (PresheafOfModules.Hom.app (tensorSumι M N.toLeftGradedModule p) X (x ⊗ₜ y)) := rfl

/-- The pure tensor is additive in its first factor. -/
theorem tmulPre_add_left (n : ℤ) (p : TensorIndex n) (X : Cᵒᵖ)
    (x x' : (M.piece p.1.1).val.obj X) (y : (N.toLeftGradedModule.piece p.1.2).val.obj X) :
    tmulPre M N n p X (x + x') y = tmulPre M N n p X x y + tmulPre M N n p X x' y :=
  (tmulPreBil M N n p).map_add_left X x x' y

/-- The pure tensor is additive in its second factor. -/
theorem tmulPre_add_right (n : ℤ) (p : TensorIndex n) (X : Cᵒᵖ)
    (x : (M.piece p.1.1).val.obj X) (y y' : (N.toLeftGradedModule.piece p.1.2).val.obj X) :
    tmulPre M N n p X x (y + y') = tmulPre M N n p X x y + tmulPre M N n p X x y' :=
  map_add ((tmulPreBil M N n p).app X x) y y'

/-- The pure tensor is linear over the base in its first factor. -/
theorem tmulPre_smul_left (n : ℤ) (p : TensorIndex n) (X : Cᵒᵖ)
    (r : (Osharp.obj ⋙ forget₂ CommRingCat RingCat).obj X)
    (x : (M.piece p.1.1).val.obj X) (y : (N.toLeftGradedModule.piece p.1.2).val.obj X) :
    tmulPre M N n p X (r • x) y = r • tmulPre M N n p X x y :=
  (tmulPreBil M N n p).map_smul_left X r x y

/-- The pure tensor is linear over the base in its second factor. -/
theorem tmulPre_smul_right (n : ℤ) (p : TensorIndex n) (X : Cᵒᵖ)
    (r : (Osharp.obj ⋙ forget₂ CommRingCat RingCat).obj X)
    (x : (M.piece p.1.1).val.obj X) (y : (N.toLeftGradedModule.piece p.1.2).val.obj X) :
    tmulPre M N n p X x (r • y) = r • tmulPre M N n p X x y :=
  (tmulPreBil M N n p).map_smul_right X r x y

/-- The restriction of `x ⊗ y` is the pure tensor of the restrictions of `x` and `y`. -/
theorem tmulPre_restr (n : ℤ) (p : TensorIndex n) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : (M.piece p.1.1).val.obj X) (y : (N.toLeftGradedModule.piece p.1.2).val.obj X) :
    restr (gradedTensorPre M N.toLeftGradedModule n) f (tmulPre M N n p X x y) =
      tmulPre M N n p Y (restr (M.piece p.1.1).val f x)
        (restr (N.toLeftGradedModule.piece p.1.2).val f y) :=
  (tmulPreBil M N n p).restr_bil f x y

/-- Pure tensors of propositionally equal indices and heterogeneously equal arguments agree. -/
theorem tmulPre_congr (n : ℤ) {p p' : TensorIndex n} (hp : p = p') (X : Cᵒᵖ)
    {x : (M.piece p.1.1).val.obj X} {x' : (M.piece p'.1.1).val.obj X} (hx : HEq x x')
    {y : (N.toLeftGradedModule.piece p.1.2).val.obj X}
    {y' : (N.toLeftGradedModule.piece p'.1.2).val.obj X} (hy : HEq y y') :
    tmulPre M N n p X x y = tmulPre M N n p' X x' y' := by
  cases hp
  rw [eq_of_heq hx, eq_of_heq hy]

/-- **The pure tensors of the presheaf-level relative tensor product are `A`-balanced**:
`x a ⊗ y` and `x ⊗ a y` agree. -/
theorem tmulPre_balanced {n : ℤ} (j : RelationIndex n) (X : Cᵒᵖ)
    (x : (M.piece j.1.1).val.obj X) (aa : (A.piece j.1.2.1).val.obj X)
    (y : (N.toLeftGradedModule.piece j.1.2.2).val.obj X) :
    tmulPre M N n (leftIndex j) X (M.smul j.1.1 j.1.2.1 X x aa) y =
      tmulPre M N n (rightIndex j) X x
        (N.toLeftGradedModule.smul j.1.2.1 j.1.2.2 X aa y) := by
  have h : PresheafOfModules.Hom.app (balanceSummandMap M N.toLeftGradedModule j ≫
      gradedTensorπ M N.toLeftGradedModule n) X (x ⊗ₜ (aa ⊗ₜ y)) = 0 := by
    rw [balanceSummandMap_comp_gradedTensorπ]
    rfl
  exact sub_eq_zero.mp (Eq.trans (Eq.trans (map_sub (ConcreteCategory.hom
      (PresheafOfModules.Hom.app (gradedTensorπ M N.toLeftGradedModule n) X)) _ _).symm
    (congrArg (PresheafOfModules.Hom.app (gradedTensorπ M N.toLeftGradedModule n) X)
      (balanceSummandMap_tmul M N.toLeftGradedModule j X x aa y).symm)) h)

/-- The right action of a homogeneous section of `B` on a pure tensor of a summand, as an
additive map in that section. -/
noncomputable def actSummandHom (n i d : ℤ) (h : n + i = d) (p : TensorIndex n) {X V : Cᵒᵖ}
    (f : X ⟶ V) (x : (M.piece p.1.1).val.obj X)
    (y : (N.toLeftGradedModule.piece p.1.2).val.obj X) :
    (B.piece i).val.obj V →+ (gradedTensorPre M N.toLeftGradedModule d).obj V :=
  AddMonoidHom.mk'
    (fun b => tmulPre M N d (actIndex p i d h) V (restr (M.piece p.1.1).val f x)
      ((rightMulL N p.1.2 i).app V (restr (N.toLeftGradedModule.piece p.1.2).val f y) b))
    (fun b b' => by
      rw [map_add ((rightMulL N p.1.2 i).app V
        (restr (N.toLeftGradedModule.piece p.1.2).val f y)), tmulPre_add_right])

/-- `actSummandHom` sends `b` to `x|_V ⊗ (y|_V b)`. -/
@[simp]
theorem actSummandHom_apply (n i d : ℤ) (h : n + i = d) (p : TensorIndex n) {X V : Cᵒᵖ}
    (f : X ⟶ V) (x : (M.piece p.1.1).val.obj X)
    (y : (N.toLeftGradedModule.piece p.1.2).val.obj X) (b : (B.piece i).val.obj V) :
    actSummandHom M N n i d h p f x y b =
      tmulPre M N d (actIndex p i d h) V (restr (M.piece p.1.1).val f x)
        ((rightMulL N p.1.2 i).app V (restr (N.toLeftGradedModule.piece p.1.2).val f y) b) :=
  rfl

/-- The right action of `B` on a summand of the presentation: `b` sends `x ⊗ y` to
`x ⊗ (y b)`. -/
noncomputable def actSummand (n i d : ℤ) (h : n + i = d) (p : TensorIndex n) :
    tensorSummand M N.toLeftGradedModule p ⟶
      bilinHom (B.piece i).val (gradedTensorPre M N.toLeftGradedModule d) :=
  PresheafOfModules.tensorMk
    (fun X x y => hMk (fun _V f => actSummandHom.{t, v, u, z} M N n i d h p f x y)
      (fun V f r b => by
        simp only [actSummandHom_apply]
        rw [(rightMulL N p.1.2 i).map_smul_right V r
          (restr (N.toLeftGradedModule.piece p.1.2).val f y) b, tmulPre_smul_right])
      (fun V W f g b => by
        simp only [actSummandHom_apply]
        rw [tmulPre_restr, rightMulL_restr, restr_restr, restr_restr]))
    (fun X x x' y => hApp_ext fun V f b => by
      simp only [hApp_hMk, hApp_add, actSummandHom_apply]
      rw [restr_add, tmulPre_add_left])
    (fun X r x y => hApp_ext fun V f b => by
      simp only [hApp_hMk, hApp_smul, actSummandHom_apply]
      rw [restr_smul, tmulPre_smul_left])
    (fun X x y y' => hApp_ext fun V f b => by
      simp only [hApp_hMk, hApp_add, actSummandHom_apply]
      rw [restr_add, (rightMulL N p.1.2 i).map_add_left, tmulPre_add_right])
    (fun X r x y => hApp_ext fun V f b => by
      simp only [hApp_hMk, hApp_smul, actSummandHom_apply]
      rw [restr_smul, (rightMulL N p.1.2 i).map_smul_left, tmulPre_smul_right])
    (fun X Y f x y => hApp_ext fun V g b => by
      simp only [hApp_hMk, hApp_restrictₛₗ, actSummandHom_apply]
      rw [restr_restrictₛₗ, restr_restrictₛₗ])

/-- The action on a summand sends `x ⊗ y` and `b` to `x|_V ⊗ (y|_V b)`. -/
theorem actSummand_tmul (n i d : ℤ) (h : n + i = d) (p : TensorIndex n) (X : Cᵒᵖ)
    (x : (M.piece p.1.1).val.obj X) (y : (N.toLeftGradedModule.piece p.1.2).val.obj X)
    {V : Cᵒᵖ} (f : X ⟶ V) (b : (B.piece i).val.obj V) :
    hApp (PresheafOfModules.Hom.app (actSummand M N n i d h p) X (x ⊗ₜ y)) f b =
      tmulPre M N d (actIndex p i d h) V (restr (M.piece p.1.1).val f x)
        ((rightMulL N p.1.2 i).app V (restr (N.toLeftGradedModule.piece p.1.2).val f y) b) :=
  congrArg (fun z => hApp z f b) (PresheafOfModules.tensorMk_tmul _ _ _ _ _ _ X x y)

/-- The right action of `B` on the direct sum of the presentation. -/
noncomputable def actSum (n i d : ℤ) (h : n + i = d) :
    tensorSum M N.toLeftGradedModule n ⟶
      bilinHom (B.piece i).val (gradedTensorPre M N.toLeftGradedModule d) :=
  Sigma.desc fun p => actSummand M N n i d h p

/-- The action on the direct sum restricts on the summand of index `p` to the action on that
summand. -/
theorem tensorSumι_actSum (n i d : ℤ) (h : n + i = d) (p : TensorIndex n) :
    tensorSumι M N.toLeftGradedModule p ≫ actSum M N n i d h = actSummand M N n i d h p :=
  Sigma.ι_comp_desc _ _

/-- The action on the direct sum sends `x ⊗ y` and `b` to `x|_V ⊗ (y|_V b)`. -/
theorem actSum_tmul (n i d : ℤ) (h : n + i = d) (p : TensorIndex n) (X : Cᵒᵖ)
    (x : (M.piece p.1.1).val.obj X) (y : (N.toLeftGradedModule.piece p.1.2).val.obj X)
    {V : Cᵒᵖ} (f : X ⟶ V) (b : (B.piece i).val.obj V) :
    hApp (PresheafOfModules.Hom.app (actSum M N n i d h) X
        (PresheafOfModules.Hom.app (tensorSumι M N.toLeftGradedModule p) X (x ⊗ₜ y))) f b =
      tmulPre M N d (actIndex p i d h) V (restr (M.piece p.1.1).val f x)
        ((rightMulL N p.1.2 i).app V (restr (N.toLeftGradedModule.piece p.1.2).val f y) b) := by
  refine Eq.trans (congrArg (fun z => hApp z f b) ?_) (actSummand_tmul M N n i d h p X x y f b)
  exact (PresheafOfModules.comp_app_apply (tensorSumι M N.toLeftGradedModule p)
    (actSum M N n i d h) X (x ⊗ₜ y)).symm.trans
    (PresheafOfModules.hom_congr_apply' (tensorSumι_actSum M N n i d h p) X (x ⊗ₜ y))

/-- **The right action of `B` respects the `A`-balancing**: `(x a) ⊗ (y b)` and `x ⊗ ((a y) b)`
agree, because the two actions on `N` commute. -/
theorem balanceMap_comp_actSum (n i d : ℤ) (h : n + i = d) :
    balanceMap M N.toLeftGradedModule n ≫ actSum M N n i d h = 0 := by
  refine Sigma.hom_ext _ _ fun j => ?_
  rw [← Category.assoc, relationSumι_balanceMap, comp_zero]
  refine PresheafOfModules.tensorObj₃_hom_ext fun X x aa y => ?_
  have hzero : PresheafOfModules.Hom.app
      (0 : relationSummand M N.toLeftGradedModule j ⟶
        bilinHom (B.piece i).val (gradedTensorPre M N.toLeftGradedModule d)) X
      (x ⊗ₜ (aa ⊗ₜ y)) = 0 := rfl
  have key : PresheafOfModules.Hom.app (actSum M N n i d h) X
      (PresheafOfModules.Hom.app (balanceSummandMap M N.toLeftGradedModule j) X
        (x ⊗ₜ (aa ⊗ₜ y))) = 0 := by
    rw [balanceSummandMap_tmul, map_sub]
    refine sub_eq_zero.mpr (hApp_ext fun V f b => ?_)
    rw [actSum_tmul, actSum_tmul, smulR_restr, smulL_restr]
    refine Eq.trans (tmulPre_balanced M N (actRelIndex j i d h) V
      (restr (M.piece j.1.1).val f x) (restr (A.piece j.1.2.1).val f aa)
      ((rightMulL N j.1.2.2 i).app V
        (restr (N.toLeftGradedModule.piece j.1.2.2).val f y) b)) ?_
    have hidx : (rightIndex (actRelIndex j i d h) : TensorIndex d) =
        actIndex (rightIndex j) i d h :=
      Subtype.ext (by simp only [Prod.mk.injEq]; exact ⟨trivial, by omega⟩)
    refine tmulPre_congr M N d hidx V HEq.rfl ?_
    exact (N.left_right_assoc j.1.2.1 j.1.2.2 i V (restr (A.piece j.1.2.1).val f aa)
      (restr (N.toLeftGradedModule.piece j.1.2.2).val f y) b).symm
  exact key.trans hzero.symm

/-- **The right action of `B` on the presheaf-level relative tensor product**, as a morphism
into an internal hom: `b` sends `x ⊗ y` to `x ⊗ (y b)`. -/
noncomputable def actPre (n i d : ℤ) (h : n + i = d) :
    gradedTensorPre M N.toLeftGradedModule n ⟶
      bilinHom (B.piece i).val (gradedTensorPre M N.toLeftGradedModule d) :=
  cokernel.desc _ (actSum.{t, v, u, z} M N n i d h)
    (balanceMap_comp_actSum.{t, v, u, z} M N n i d h)

/-- The action on the presheaf-level relative tensor product, composed with the quotient map of
the presentation, is the action on the direct sum. -/
@[simp]
theorem gradedTensorπ_actPre (n i d : ℤ) (h : n + i = d) :
    gradedTensorπ M N.toLeftGradedModule n ≫ actPre M N n i d h = actSum M N n i d h :=
  cokernel.π_desc _ _ _

/-- The right action of `B` on a pure tensor: `b` sends `x ⊗ y` to `x ⊗ (y b)`. -/
theorem actPre_tmulPre (n i d : ℤ) (h : n + i = d) (p : TensorIndex n) (X : Cᵒᵖ)
    (x : (M.piece p.1.1).val.obj X) (y : (N.toLeftGradedModule.piece p.1.2).val.obj X)
    {V : Cᵒᵖ} (f : X ⟶ V) (b : (B.piece i).val.obj V) :
    hApp (PresheafOfModules.Hom.app (actPre M N n i d h) X (tmulPre M N n p X x y)) f b =
      tmulPre M N d (actIndex p i d h) V (restr (M.piece p.1.1).val f x)
        ((rightMulL N p.1.2 i).app V (restr (N.toLeftGradedModule.piece p.1.2).val f y) b) := by
  refine Eq.trans (congrArg (fun z => hApp z f b) ?_) (actSum_tmul M N n i d h p X x y f b)
  exact (PresheafOfModules.comp_app_apply (gradedTensorπ M N.toLeftGradedModule n)
    (actPre M N n i d h) X _).symm.trans
    (PresheafOfModules.hom_congr_apply' (gradedTensorπ_actPre M N n i d h) X _)

/-- Changing the target degree of the action by a propositional equality transports its
values. -/
theorem actPre_degCast (n i d d' : ℤ) (h : n + i = d) (h' : n + i = d') (U : Cᵒᵖ)
    (z : (gradedTensorPre M N.toLeftGradedModule n).obj U) {V : Cᵒᵖ} (f : U ⟶ V)
    (b : (B.piece i).val.obj V) :
    Stacks.degCast (F := fun k => (gradedTensorPre M N.toLeftGradedModule k).obj V)
        (by omega : d = d')
        (hApp (PresheafOfModules.Hom.app (actPre M N n i d h) U z) f b) =
      hApp (PresheafOfModules.Hom.app (actPre M N n i d' h') U z) f b := by
  obtain rfl : d = d' := by omega
  rfl

/-- Two morphisms out of the presheaf-level relative tensor product agree if they agree on pure
tensors. -/
private theorem gradedTensorPre_hom_ext {n : ℤ}
    {P : PresheafOfModules.{max u v z} (Osharp.obj ⋙ forget₂ CommRingCat RingCat)}
    {f g : gradedTensorPre M N.toLeftGradedModule n ⟶ P}
    (h : ∀ (p : TensorIndex n) (X : Cᵒᵖ) (x : (M.piece p.1.1).val.obj X)
      (y : (N.toLeftGradedModule.piece p.1.2).val.obj X),
      PresheafOfModules.Hom.app f X (tmulPre M N n p X x y) =
        PresheafOfModules.Hom.app g X (tmulPre M N n p X x y)) : f = g :=
  (cancel_epi (gradedTensorπ M N.toLeftGradedModule n)).mp
    (Sigma.hom_ext _ _ fun p => PresheafOfModules.tensorObj_hom_ext fun X x y => h p X x y)

/-- **Associativity of the right action**, at the presheaf level: acting by `b` and then by `b'`
is acting by `b b'`. -/
theorem actPre_assoc (n i j d₁ d : ℤ) (h₁ : n + i = d₁) (h₂ : d₁ + j = d)
    (h₃ : n + (i + j) = d) :
    actPre M N n i d₁ h₁ ≫ bilinHomMap (B.piece i).val (actPre M N d₁ j d h₂) =
      actPre M N n (i + j) d h₃ ≫
        bilinHomUncurry (B.mul i j) (gradedTensorPre M N.toLeftGradedModule d) := by
  refine gradedTensorPre_hom_ext M N fun p X x y => hApp_ext fun V f b => hApp_ext fun W g b' => ?_
  change hApp (hApp (PresheafOfModules.Hom.app
      (bilinHomMap (B.piece i).val (actPre M N d₁ j d h₂)) X
      (PresheafOfModules.Hom.app (actPre M N n i d₁ h₁) X (tmulPre M N n p X x y))) f b) g b' =
    hApp (hApp (PresheafOfModules.Hom.app
      (bilinHomUncurry (B.mul i j) (gradedTensorPre M N.toLeftGradedModule d)) X
      (PresheafOfModules.Hom.app (actPre M N n (i + j) d h₃) X (tmulPre M N n p X x y))) f b) g b'
  rw [hApp_bilinHomMap, actPre_tmulPre, actPre_tmulPre, hApp_bilinHomUncurry, actPre_tmulPre]
  have hidx : actIndex (actIndex p i d₁ h₁) j d h₂ = actIndex p (i + j) d h₃ :=
    Subtype.ext (by simp only [Prod.mk.injEq]; exact ⟨trivial, by omega⟩)
  refine tmulPre_congr M N d hidx W
    (heq_of_eq (restr_restr (M.piece p.1.1).val f g x)) ?_
  rw [rightMulL_restr, restr_restr]
  exact N.right_assoc p.1.2 i j W (restr (N.toLeftGradedModule.piece p.1.2).val (f ≫ g) y)
    (restr (B.piece i).val g b) b'

/-- Associativity of the right action, read on local sections. -/
theorem actPre_assoc_apply (n i j d₁ d : ℤ) (h₁ : n + i = d₁) (h₂ : d₁ + j = d)
    (h₃ : n + (i + j) = d) (U : Cᵒᵖ) (z : (gradedTensorPre M N.toLeftGradedModule n).obj U)
    (b : (B.piece i).val.obj U) (b' : (B.piece j).val.obj U) :
    hApp (PresheafOfModules.Hom.app (actPre M N d₁ j d h₂) U
        (hApp (PresheafOfModules.Hom.app (actPre M N n i d₁ h₁) U z) (𝟙 U) b)) (𝟙 U) b' =
      hApp (PresheafOfModules.Hom.app (actPre M N n (i + j) d h₃) U z) (𝟙 U)
        ((B.mul i j).app U b b') := by
  refine Eq.trans (congrArg (fun w => hApp (hApp w (𝟙 U) b) (𝟙 U) b')
    (PresheafOfModules.hom_congr_apply (actPre_assoc M N n i j d₁ d h₁ h₂ h₃) U z)) ?_
  change hApp (hApp (PresheafOfModules.Hom.app
      (bilinHomUncurry (B.mul i j) (gradedTensorPre M N.toLeftGradedModule d)) U
      (PresheafOfModules.Hom.app (actPre M N n (i + j) d h₃) U z)) (𝟙 U) b) (𝟙 U) b' = _
  rw [hApp_bilinHomUncurry, Category.id_comp, restr_id]

/-- **Unitality of the right action**, at the presheaf level: the unit of `B` acts as the
identity. -/
theorem actPre_one (n : ℤ) :
    actPre M N n 0 n (add_zero n) ≫
        bilinHomEval B.one (gradedTensorPre M N.toLeftGradedModule n) =
      𝟙 (gradedTensorPre M N.toLeftGradedModule n) := by
  refine gradedTensorPre_hom_ext M N fun p X x y => ?_
  change hApp (PresheafOfModules.Hom.app (actPre M N n 0 n (add_zero n)) X
    (tmulPre M N n p X x y)) (𝟙 X) (B.one.eval X) = tmulPre M N n p X x y
  rw [actPre_tmulPre, restr_id, restr_id]
  have hidx : actIndex p 0 n (add_zero n) = p := Subtype.ext (by simp)
  exact tmulPre_congr M N n hidx X HEq.rfl (N.one_right p.1.2 X y)

/-- **The right action of `B` on the presheaf-level relative tensor product**, assembled into a
presheaf-level right graded `B`-module. -/
noncomputable def preGradedModule : PreGradedModule.{t, max u v z, max u v z} B where
  piece n := gradedTensorPre M N.toLeftGradedModule n
  smulBil n i := Stacks.toBilinHom (actPre M N n i (n + i) rfl)
  smulBil_assoc n i j U z b b' :=
    (congrArg (Stacks.degCast
        (F := fun k => (gradedTensorPre M N.toLeftGradedModule k).obj U) (add_assoc n i j))
      (actPre_assoc_apply M N n i j (n + i) (n + i + j) rfl rfl (by omega) U z b b')).trans
      (actPre_degCast M N n (i + j) (n + i + j) (n + (i + j)) (by omega) rfl U z (𝟙 U)
        ((B.mul i j).app U b b'))
  smulBil_one n U z :=
    (actPre_degCast M N n 0 (n + 0) n rfl (add_zero n) U z (𝟙 U) (B.one.eval U)).trans
      (PresheafOfModules.hom_congr_apply (actPre_one M N n) U z)

/-- Degree `n` of `preGradedModule M N` is degree `n` of the presheaf-level relative tensor
product. -/
@[simp]
theorem preGradedModule_piece (n : ℤ) :
    (preGradedModule M N).piece n = gradedTensorPre M N.toLeftGradedModule n := rfl

/-- The action of `b` on `z` in `preGradedModule M N` is the identity component of
`actPre M N n i (n + i) rfl` at `z`, evaluated at `b`. -/
theorem preGradedModule_smulBil_app (n i : ℤ) (U : Cᵒᵖ)
    (z : (gradedTensorPre M N.toLeftGradedModule n).obj U) (b : (B.piece i).val.obj U) :
    ((preGradedModule M N).smulBil n i).app U z b =
      hApp (PresheafOfModules.Hom.app (actPre M N n i (n + i) rfl) U z) (𝟙 U) b := rfl

section Sheafify

variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v z}]
  [HasWeakSheafify J AddCommGrpCat.{max u v z}]

/-- The sheafification map of a presheaf-level graded module over the sheaf of rings underlying
a sheaf of commutative rings is locally surjective. -/
instance isLocallySurjective_toSheafifyPiece (P : PreGradedModule.{t, max u v z, max u v z} B)
    (n : ℤ) : PresheafOfModules.IsLocallySurjective J (P.toSheafifyPiece n) := by
  have h : Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf
      (toRingCat J Osharp).obj).map (P.toSheafifyPiece n)) := by
    rw [P.toPresheaf_map_toSheafifyPiece n]
    exact (J.W_toSheafify (P.piece n).presheaf).isLocallySurjective
  exact h

/-- The sheafification map of a presheaf-level graded module is locally injective. -/
instance isLocallyInjective_toSheafifyPiece (P : PreGradedModule.{t, max u v z, max u v z} B)
    (n : ℤ) : PresheafOfModules.IsLocallyInjective J (P.toSheafifyPiece n) := by
  have h : Presheaf.IsLocallyInjective J ((PresheafOfModules.toPresheaf
      (toRingCat J Osharp).obj).map (P.toSheafifyPiece n)) := by
    rw [P.toPresheaf_map_toSheafifyPiece n]
    exact (J.W_toSheafify (P.piece n).presheaf).isLocallyInjective
  exact h

/-- **Stacks 0FR4: the right graded `B`-module `M ⊗_A N`**, for `M` a right graded `A`-module and
`N` a graded `(A, B)`-bimodule: degree `n` is degree `n` of the graded tensor product of Stacks
0FR2, and a homogeneous section `b` of `B` acts on `x ⊗ y` by `x ⊗ (y b)`
(`SheafOfModules.RelativeTensor.gradedTensorRight_smul_tmul`). The functors `- ⊗_A N` are
`SheafOfModules.RelativeTensor.gradedTensorRightFunctor` and
`SheafOfModules.RelativeTensor.gradedTensorRightHomOfDegree`, with the laws of a functor of graded
categories in `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedBimoduleTensorFunctor.lean`. -/
@[stacks 0FR4 "M ⊗_A N is a right graded B-module, with (x ⊗ y) b = x ⊗ (y b)"]
noncomputable def gradedTensorRight : GradedModule.{t, max u v z, max u v z} B :=
  (preGradedModule M N).sheafify

/-- Degree `n` of `gradedTensorRight M N` is degree `n` of the graded relative tensor product. -/
@[simp]
theorem gradedTensorRight_piece (n : ℤ) :
    (gradedTensorRight M N).piece n = gradedTensor M N.toLeftGradedModule n := rfl

/-- **The right action of `B` on a local section `x ⊗ y`**: it is `x ⊗ (y b)`. -/
theorem gradedTensorRight_smul_tmul (n i : ℤ) (p : TensorIndex n) (X : Cᵒᵖ)
    (x : (M.piece p.1.1).val.obj X) (y : (N.toLeftGradedModule.piece p.1.2).val.obj X)
    (b : (B.piece i).val.obj X) :
    (gradedTensorRight M N).smul n i X (tmul M N.toLeftGradedModule n p X x y) b =
      tmul M N.toLeftGradedModule (n + i) (actIndex p i (n + i) rfl) X x
        ((rightMulL N p.1.2 i).app X y b) := by
  refine Eq.trans ((preGradedModule M N).sheafify_smul n i X (tmulPre M N n p X x y) b) ?_
  refine congrArg (PresheafOfModules.Hom.app
    ((preGradedModule M N).toSheafifyPiece (n + i)) X) ?_
  rw [preGradedModule_smulBil_app, actPre_tmulPre, restr_id, restr_id]
  rfl

/-- A degreewise family of `A`-balanced bilinear families into a right graded `B`-module which
is compatible with the right actions: `x ⊗ (y b)` has the value of `(x ⊗ y) b`. -/
structure BalancedRight (K : GradedModule.{t, max u v z, max u v z} B) where
  /-- The balanced bilinear family of each total degree. -/
  app (n : ℤ) : Balanced M N.toLeftGradedModule (K.piece n).val n
  /-- The family is `B`-linear in its second variable. -/
  map_smul (n i : ℤ) (p : TensorIndex n) (U : Cᵒᵖ) (x : (M.piece p.1.1).val.obj U)
      (y : (N.toLeftGradedModule.piece p.1.2).val.obj U) (b : (B.piece i).val.obj U) :
    ((app (n + i)).app (actIndex p i (n + i) rfl)).app U x
        ((rightMulL N p.1.2 i).app U y b) =
      K.smul n i U (((app n).app p).app U x y) b

namespace BalancedRight

variable {M N} {K : GradedModule.{t, max u v z, max u v z} B} (β : BalancedRight M N K)

/-- The descent of the balanced bilinear family of one total degree. -/
noncomputable def descHom (n : ℤ) : gradedTensor M N.toLeftGradedModule n ⟶ K.piece n :=
  (β.app n).desc M N.toLeftGradedModule

/-- The descent of one total degree sends `x ⊗ y` to the value of the balanced family at `x` and
`y`. -/
theorem descHom_tmul (n : ℤ) (p : TensorIndex n) (X : Cᵒᵖ) (x : (M.piece p.1.1).val.obj X)
    (y : (N.toLeftGradedModule.piece p.1.2).val.obj X) :
    PresheafOfModules.Hom.app (β.descHom n).val X (tmul M N.toLeftGradedModule n p X x y) =
      ((β.app n).app p).app X x y :=
  Balanced.desc_tmul M N.toLeftGradedModule (β.app n) p X x y

/-- The sheafification unit followed by the descent sends the presheaf-level pure tensor `x ⊗ y`
to the value of the balanced family at `x` and `y`. -/
theorem descHom_tmulPre (n : ℤ) (p : TensorIndex n) (X : Cᵒᵖ) (x : (M.piece p.1.1).val.obj X)
    (y : (N.toLeftGradedModule.piece p.1.2).val.obj X) :
    PresheafOfModules.Hom.app ((preGradedModule M N).toSheafifyPiece n ≫
        (β.descHom n).val) X (tmulPre M N n p X x y) = ((β.app n).app p).app X x y :=
  β.descHom_tmul n p X x y

/-- The descent is `B`-linear on the presheaf-level relative tensor product. -/
theorem actPre_comp_descHom (n i : ℤ) :
    actPre M N n i (n + i) rfl ≫ bilinHomMap (B.piece i).val
        ((preGradedModule M N).toSheafifyPiece (n + i) ≫ (β.descHom (n + i)).val) =
      ofBilinHom ((K.smulBil n i).compLeft
        ((preGradedModule M N).toSheafifyPiece n ≫ (β.descHom n).val)) := by
  refine gradedTensorPre_hom_ext M N fun p X x y => hApp_ext fun V f b => ?_
  change PresheafOfModules.Hom.app ((preGradedModule M N).toSheafifyPiece (n + i) ≫
      (β.descHom (n + i)).val) V
      (hApp (PresheafOfModules.Hom.app (actPre M N n i (n + i) rfl) X
        (tmulPre M N n p X x y)) f b) =
    (K.smulBil n i).app V (PresheafOfModules.Hom.app
      ((preGradedModule M N).toSheafifyPiece n ≫ (β.descHom n).val) V
        (restr (gradedTensorPre M N.toLeftGradedModule n) f (tmulPre M N n p X x y))) b
  rw [actPre_tmulPre, tmulPre_restr, descHom_tmulPre, descHom_tmulPre]
  exact β.map_smul n i p V (restr (M.piece p.1.1).val f x)
    (restr (N.toLeftGradedModule.piece p.1.2).val f y) b

/-- **The universal property of `M ⊗_A N` survives the right action**: a degreewise family of
`A`-balanced bilinear families which is `B`-linear in its second variable descends to a
homomorphism of right graded `B`-modules out of `M ⊗_A N`. -/
noncomputable def descRight : gradedTensorRight M N ⟶ K where
  app n := β.descHom n
  map_smul n i U z b := by
    refine (preGradedModule M N).hom_map_smul (preGradedModule M N).sheafifyPiece
      (preGradedModule M N).toSheafifyPiece K (fun n => β.descHom n) ?_ n i U z b
    intro n' i' U' z' b'
    refine Eq.trans (congrArg (fun w => hApp w (𝟙 U') b')
      (PresheafOfModules.hom_congr_apply (β.actPre_comp_descHom n' i') U' z')) ?_
    change (K.smulBil n' i').app U' (PresheafOfModules.Hom.app
        ((preGradedModule M N).toSheafifyPiece n' ≫ (β.descHom n').val) U'
        (restr ((preGradedModule M N).piece n') (𝟙 U') z')) b' = _
    rw [restr_id]
    rfl

/-- Degree `n` of `descRight` is the descent of degree `n`. -/
@[simp]
theorem descRight_app (n : ℤ) : β.descRight.app n = β.descHom n := rfl

/-- The descent on a local section `x ⊗ y`. -/
theorem descRight_tmul (n : ℤ) (p : TensorIndex n) (X : Cᵒᵖ) (x : (M.piece p.1.1).val.obj X)
    (y : (N.toLeftGradedModule.piece p.1.2).val.obj X) :
    PresheafOfModules.Hom.app (β.descRight.app n).val X
        (tmul M N.toLeftGradedModule n p X x y) = ((β.app n).app p).app X x y :=
  β.descHom_tmul n p X x y

end BalancedRight

end Sheafify

end RelativeTensor

end SheafOfModules
