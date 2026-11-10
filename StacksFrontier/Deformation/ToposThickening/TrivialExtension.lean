module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SplitSquareZeroModule
public import StacksFrontier.Deformation.ToposThickening.ModulesOnThickening.ActionMapUnique
public import StacksFrontier.Deformation.ToposThickening.ModulesOnThickening.FixedAction
public import StacksFrontier.Deformation.ToposThickening.TrivialExtensionClass

/-!
# The trivial extension over a trivialized first order thickening of ringed topoi

Let `i : (Sh(C), O) ⟶ (Sh(D), O')` be a first order thickening of ringed topoi with square-zero
ideal `I`, and let `π` be a trivialization of it. Write `q : O' ⟶ O` for the structure map and
`π^♯ : O ⟶ O'` for the splitting of `q` supplied by `π`, so that `O' = O ⊕ I`. Given
`O`-modules `F` and `K` and a map `c : I ⊗_O F ⟶ K`, the sheaf `F ⊕ K` with the action

    r · (m, k) = (q r · m, q r · k + c(d r ⊗ m)),        d r = r - π^♯(q r),

is an `O'`-module `F'_{c,triv}`, the *trivial extension*, sitting in an extension
`0 ⟶ K ⟶ F'_{c,triv} ⟶ F ⟶ 0` as in Stacks 08MB whose canonical map is `c`. Reading an
extension `F'` as an `O`-module along `π^♯` gives a class `ξ_{F'} ∈ Ext¹_O(F, K)`, and
`F' ↦ ξ_{F'}` is a bijection from the isomorphism classes of extensions with `c_{F'} = c` onto
`Ext¹_O(F, K)` sending the trivial extension to zero. This is Stacks 08MI.

## Main definitions

* `Deformation.ToposThickening.trivializationDerivation`: the derivation `d : O' ⟶ I` of the
  splitting, on sections.
* `Deformation.ToposThickening.trivialExtensionModule` and
  `Deformation.ToposThickening.trivialExtension`: the trivial extension `F'_{c,triv}`, as a module
  and as an extension.
* `Deformation.ToposThickening.splitRestrictionExtHom`: the homomorphism
  `Ext¹_{O'}(F, K) ⟶ Ext¹_O(F, K)` of reading an extension along `π^♯`.

## Main results

* `Deformation.ToposThickening.trivialExtension_extensionActionMap`: `c_{F'_{c,triv}} = c`.
* `Deformation.ToposThickening.underlyingExtensionClass_trivialExtension`:
  `ξ_{F'_{c,triv}} = 0`.
* `Deformation.ToposThickening.trivialExtension_bijective_underlyingExtensionClass`:
  **Stacks 08MI**.

## Implementation notes

The module structure is `Stacks.SheafOfModules.SplitSquareZero.extensionSheafModule`, applied
to the derivation and to `c` read on pure tensors of local sections
(`Deformation.ToposThickening.extensionPairing`). The derivation is produced as a section of
the ideal through the kernel property of the thickening and is unique by injectivity of the
inclusion of the ideal, so every law it satisfies is a ring identity in `O'(U)`; the Leibniz rule
is the only place where the square-zero property is used.

The isomorphism classes of extensions with `c_{F'} = c` are represented, as in Stacks 08ME, by
their classes in `Ext¹_{O'}(F, K)` (`Deformation.ToposThickening.FixedActionExtensionClass`); two
short exact sequences have the same class exactly when they are isomorphic over both end terms.
The statement of 08MI also gives the bijection directly on extensions. The bijection is the
coset description of the classes with a fixed action
(`Deformation.ToposThickening.exists_extensionActionMap_eq_iff_exists_add_mapExtAddHom`) together
with the fact that reading along `π^♯` undoes the restriction of scalars along `q`
(`Deformation.ToposThickening.splitRestrictionExtHom_mapExtAddHom`), the trivial extension
supplying the base point.

The bilinearity laws of the pairing are proved in term mode: the scalar ring of the tensor product
of sections is spelled `O(U)` in one place and through `forget₂ CommRingCat RingCat` in another,
and `rw` rejects motives mixing the two, while the elaborator identifies them.

## References

* [Stacks Project, Tag 08MI](https://stacks.math.columbia.edu/tag/08MI)
* [Stacks Project, Tag 08MH](https://stacks.math.columbia.edu/tag/08MH)
* [Stacks Project, Tag 08MB](https://stacks.math.columbia.edu/tag/08MB)
* [Stacks Project, Tag 08ME](https://stacks.math.columbia.edu/tag/08ME)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TensorProduct
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor)

universe e v u w v' u' w'

namespace Deformation.ToposThickening

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  {i : RingedToposHom X Y}

/-! ### The derivation attached to a trivialization -/

section Derivation

variable (hi : FirstOrderThickening i) (π : Trivialization i)

/-- The inclusion of the square-zero ideal into the structure sheaf, on sections. -/
noncomputable def idealSection (U : Y.Cᵒᵖ) (a : hi.I.val.obj U) :
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U :=
  hi.incl.val.app U a

/-- The structure map `q : O' ⟶ O`, on sections. -/
noncomputable def structureApp (i : RingedToposHom X Y) (U : Y.Cᵒᵖ)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U) :
    (Stacks.SheafOfModules.Tensor.ringSheaf
      ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj.obj U :=
  ((show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
      Stacks.SheafOfModules.Tensor.ringSheaf
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
    (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp).hom.app U).hom r

/-- The splitting `π^♯ : O ⟶ O'` of the structure map, on sections. -/
noncomputable def splitApp (U : Y.Cᵒᵖ)
    (a : (Stacks.SheafOfModules.Tensor.ringSheaf
      ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj.obj U) :
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U :=
  ((splittingRingHom i hi π).hom.app U).hom a

theorem structureApp_splitApp (U : Y.Cᵒᵖ)
    (a : (Stacks.SheafOfModules.Tensor.ringSheaf
      ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj.obj U) :
    structureApp i U (splitApp hi π U a) = a :=
  congrArg (fun f => (f.hom.app U).hom a) (splittingRingHom_comp i hi π)

theorem idealSection_zero (U : Y.Cᵒᵖ) : idealSection hi U 0 = 0 :=
  map_zero (hi.incl.val.app U).hom

theorem idealSection_add (U : Y.Cᵒᵖ) (a b : hi.I.val.obj U) :
    idealSection hi U (a + b) = idealSection hi U a + idealSection hi U b :=
  map_add (hi.incl.val.app U).hom a b

/-- The inclusion of the ideal is linear over the structure sheaf of the thickening, which acts on
the ideal through the structure map. -/
theorem idealSection_smul (U : Y.Cᵒᵖ) (r : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U)
    (a : hi.I.val.obj U) :
    idealSection hi U (structureApp i U r • a) = r * idealSection hi U a :=
  (hi.incl.val.app U).hom.map_smul r
    (show ((SheafOfModules.restrictScalars
      (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
      Stacks.SheafOfModules.Tensor.ringSheaf
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
    (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj hi.I).val.obj U from a)

theorem idealSection_naturality {U V : Y.Cᵒᵖ} (f : U ⟶ V) (a : hi.I.val.obj U) :
    idealSection hi V (hi.I.val.map f a) =
      ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.map f).hom (idealSection hi U a) :=
  PresheafOfModules.naturality_apply hi.incl.val f a

theorem idealSection_mul_idealSection (U : Y.Cᵒᵖ) (a b : hi.I.val.obj U) :
    idealSection hi U a * idealSection hi U b = 0 :=
  hi.square_zero U a b

theorem structureApp_naturality {U V : Y.Cᵒᵖ} (f : U ⟶ V)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U) :
    structureApp i V (((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.map f).hom r) =
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj.map f).hom
        (structureApp i U r) :=
  congrArg (fun g => g.hom r)
    ((show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
      Stacks.SheafOfModules.Tensor.ringSheaf
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
    (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp).hom.naturality f)

theorem splitApp_naturality {U V : Y.Cᵒᵖ} (f : U ⟶ V)
    (a : (Stacks.SheafOfModules.Tensor.ringSheaf
      ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj.obj U) :
    splitApp hi π V (((Stacks.SheafOfModules.Tensor.ringSheaf
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj.map f).hom a) =
      ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.map f).hom (splitApp hi π U a) :=
  congrArg (fun g => g.hom a) ((splittingRingHom i hi π).hom.naturality f)

theorem idealSection_injective (U : Y.Cᵒᵖ) : Function.Injective (idealSection hi U) :=
  hi.injective U

theorem structureApp_idealSection (U : Y.Cᵒᵖ) (a : hi.I.val.obj U) :
    structureApp i U (idealSection hi U a) = 0 :=
  (hi.kernel U _).2 ⟨a, rfl⟩

/-- The remainder `r - π^♯(q r)` of a section under the splitting lies in the ideal. -/
theorem exists_idealSection_eq_sub (U : Y.Cᵒᵖ)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U) :
    ∃ b : hi.I.val.obj U, idealSection hi U b = r - splitApp hi π U (structureApp i U r) := by
  refine (hi.kernel U _).1 ?_
  change structureApp i U (r - splitApp hi π U (structureApp i U r)) = 0
  rw [structureApp, map_sub]
  change structureApp i U r - structureApp i U (splitApp hi π U (structureApp i U r)) = 0
  rw [structureApp_splitApp, sub_self]

/-- **The derivation of a trivialization.** On sections, `d r = r - π^♯(q r)`, read as a section
of the square-zero ideal. -/
noncomputable def trivializationDerivation (U : Y.Cᵒᵖ)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U) : hi.I.val.obj U :=
  (exists_idealSection_eq_sub hi π U r).choose

theorem idealSection_trivializationDerivation (U : Y.Cᵒᵖ)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U) :
    idealSection hi U (trivializationDerivation hi π U r) =
      r - splitApp hi π U (structureApp i U r) :=
  (exists_idealSection_eq_sub hi π U r).choose_spec

theorem trivializationDerivation_zero (U : Y.Cᵒᵖ) : trivializationDerivation hi π U 0 = 0 := by
  refine idealSection_injective hi U ?_
  rw [idealSection_trivializationDerivation, idealSection_zero, structureApp, map_zero,
    splitApp, map_zero, sub_zero]

theorem trivializationDerivation_one (U : Y.Cᵒᵖ) : trivializationDerivation hi π U 1 = 0 := by
  refine idealSection_injective hi U ?_
  rw [idealSection_trivializationDerivation, idealSection_zero, structureApp, map_one,
    splitApp, map_one, sub_self]

theorem trivializationDerivation_add (U : Y.Cᵒᵖ)
    (r s : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U) :
    trivializationDerivation hi π U (r + s) =
      trivializationDerivation hi π U r + trivializationDerivation hi π U s := by
  refine idealSection_injective hi U ?_
  rw [idealSection_add, idealSection_trivializationDerivation,
    idealSection_trivializationDerivation,
    idealSection_trivializationDerivation, structureApp, map_add, splitApp, map_add]
  abel

/-- **The Leibniz rule** for the derivation of a trivialization: `d(rs) = r · d s + s · d r`,
where the structure sheaf of the thickening acts on the ideal through the structure map. The
square-zero hypothesis enters here and only here. -/
theorem trivializationDerivation_mul (U : Y.Cᵒᵖ)
    (r s : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U) :
    trivializationDerivation hi π U (r * s) =
      structureApp i U r • trivializationDerivation hi π U s +
        structureApp i U s • trivializationDerivation hi π U r := by
  refine idealSection_injective hi U ?_
  have hz := idealSection_mul_idealSection hi U (trivializationDerivation hi π U r)
    (trivializationDerivation hi π U s)
  rw [idealSection_trivializationDerivation, idealSection_trivializationDerivation] at hz
  rw [idealSection_add, idealSection_smul, idealSection_smul,
    idealSection_trivializationDerivation, idealSection_trivializationDerivation,
    idealSection_trivializationDerivation, structureApp, map_mul, splitApp, map_mul]
  have key : ∀ (A : Type w') [CommRing A] (r s x y : A), (r - x) * (s - y) = 0 →
      r * s - x * y = r * (s - y) + s * (r - x) := by
    intro A _ r s x y h
    linear_combination -h
  exact key (Y.O.obj.obj U) r s _ _ hz

theorem trivializationDerivation_naturality {U V : Y.Cᵒᵖ} (f : U ⟶ V)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U) :
    hi.I.val.map f (trivializationDerivation hi π U r) =
      trivializationDerivation hi π V
        (((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.map f).hom r) := by
  refine idealSection_injective hi V ?_
  rw [idealSection_naturality, idealSection_trivializationDerivation,
    idealSection_trivializationDerivation, map_sub, structureApp_naturality, splitApp_naturality]

/-- The derivation is the identity on the ideal: `d(ι a) = a`. -/
theorem trivializationDerivation_idealSection (U : Y.Cᵒᵖ) (a : hi.I.val.obj U) :
    trivializationDerivation hi π U (idealSection hi U a) = a := by
  refine idealSection_injective hi U ?_
  rw [idealSection_trivializationDerivation, structureApp_idealSection, splitApp, map_zero,
    sub_zero]

/-- The derivation kills the image of the splitting: `d(π^♯ a) = 0`. -/
theorem trivializationDerivation_splitApp (U : Y.Cᵒᵖ)
    (a : (Stacks.SheafOfModules.Tensor.ringSheaf
      ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj.obj U) :
    trivializationDerivation hi π U (splitApp hi π U a) = 0 := by
  refine idealSection_injective hi U ?_
  rw [idealSection_trivializationDerivation, idealSection_zero, structureApp_splitApp, sub_self]

end Derivation

/-! ### The prescribed map `c` on sections -/

section Pairing

/-! The sheaf of rings of the ringed topos is spelled `Stacks.SheafOfModules.Tensor.ringSheaf`,
while `SheafOfModules.restrictScalars` and the module categories reach it through
`CategoryTheory.sheafCompose`. The two are definitionally equal but not reducibly equal, so the
attribute block, local to this section, lists the definitions along the way between them. -/

attribute [local implicit_reducible] SheafOfModules.unit PresheafOfModules.unit
  CategoryTheory.ConcreteCategory.hom CategoryTheory.sheafCompose SheafOfModules.forget
  SheafOfModules.restrictScalars PresheafOfModules.restrictScalars ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj' PresheafOfModules.restrictScalarsObj

variable [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
  (hi : FirstOrderThickening i)
  (F K : SheafOfModules.{w'}
    (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))
  (c : ((Stacks.SheafOfModules.Tensor.sheafTensor
    ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj hi.I).obj F ⟶ K)

/-- The value of `c : I ⊗_O F ⟶ K` on a pure tensor of local sections. -/
noncomputable def extensionPairing (U : Y.Cᵒᵖ) (a : hi.I.val.obj U) (m : F.val.obj U) :
    K.val.obj U :=
  c.val.app U (((PresheafOfModules.sheafificationAdjunction
      (R := Stacks.SheafOfModules.Tensor.ringSheaf
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O))
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj)).unit.app
      (PresheafOfModules.tensorObj hi.I.val F.val)).app U
    (a ⊗ₜ[((pushforwardCommRingFunctor i.toToposHom).obj X.O).obj.obj U] m))

/-- The pairing of a pure tensor which is a sum of pure tensors is the sum of the pairings. -/
private theorem extensionPairing_eq_add {U : Y.Cᵒᵖ} {a a₁ a₂ : hi.I.val.obj U}
    {m m₁ m₂ : F.val.obj U}
    (h : a ⊗ₜ[((pushforwardCommRingFunctor i.toToposHom).obj X.O).obj.obj U] m =
      a₁ ⊗ₜ[((pushforwardCommRingFunctor i.toToposHom).obj X.O).obj.obj U] m₁ +
        a₂ ⊗ₜ[((pushforwardCommRingFunctor i.toToposHom).obj X.O).obj.obj U] m₂) :
    extensionPairing hi F K c U a m =
      extensionPairing hi F K c U a₁ m₁ + extensionPairing hi F K c U a₂ m₂ :=
  (congrArg (fun z => c.val.app U (((PresheafOfModules.sheafificationAdjunction
      (R := Stacks.SheafOfModules.Tensor.ringSheaf
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O))
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj)).unit.app
      (PresheafOfModules.tensorObj hi.I.val F.val)).app U z)) h).trans
    ((congrArg (c.val.app U) (map_add _ _ _)).trans (map_add _ _ _))

/-- The pairing of a pure tensor which is a scalar multiple of a pure tensor is the scalar
multiple of the pairing. -/
private theorem extensionPairing_eq_smul {U : Y.Cᵒᵖ}
    {r : ((pushforwardCommRingFunctor i.toToposHom).obj X.O).obj.obj U}
    {a a' : hi.I.val.obj U} {m m' : F.val.obj U}
    (h : a ⊗ₜ[((pushforwardCommRingFunctor i.toToposHom).obj X.O).obj.obj U] m =
      r • (a' ⊗ₜ[((pushforwardCommRingFunctor i.toToposHom).obj X.O).obj.obj U] m')) :
    extensionPairing hi F K c U a m = r • extensionPairing hi F K c U a' m' :=
  (congrArg (fun z => c.val.app U (((PresheafOfModules.sheafificationAdjunction
      (R := Stacks.SheafOfModules.Tensor.ringSheaf
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O))
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj)).unit.app
      (PresheafOfModules.tensorObj hi.I.val F.val)).app U z)) h).trans
    ((congrArg (c.val.app U) (map_smul _ _ _)).trans (map_smul _ _ _))

/-- The pairing of a vanishing pure tensor is zero. -/
private theorem extensionPairing_eq_zero {U : Y.Cᵒᵖ} {a : hi.I.val.obj U} {m : F.val.obj U}
    (h : a ⊗ₜ[((pushforwardCommRingFunctor i.toToposHom).obj X.O).obj.obj U] m = 0) :
    extensionPairing hi F K c U a m = 0 :=
  (congrArg (fun z => c.val.app U (((PresheafOfModules.sheafificationAdjunction
      (R := Stacks.SheafOfModules.Tensor.ringSheaf
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O))
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj)).unit.app
      (PresheafOfModules.tensorObj hi.I.val F.val)).app U z)) h).trans
    ((congrArg (c.val.app U) (map_zero _)).trans (map_zero _))

theorem extensionPairing_add_left (U : Y.Cᵒᵖ) (a b : hi.I.val.obj U) (m : F.val.obj U) :
    extensionPairing hi F K c U (a + b) m =
      extensionPairing hi F K c U a m + extensionPairing hi F K c U b m :=
  extensionPairing_eq_add hi F K c (TensorProduct.add_tmul a b m)

theorem extensionPairing_add_right (U : Y.Cᵒᵖ) (a : hi.I.val.obj U) (m n : F.val.obj U) :
    extensionPairing hi F K c U a (m + n) =
      extensionPairing hi F K c U a m + extensionPairing hi F K c U a n :=
  extensionPairing_eq_add hi F K c (TensorProduct.tmul_add a m n)

theorem extensionPairing_zero_right (U : Y.Cᵒᵖ) (a : hi.I.val.obj U) :
    extensionPairing hi F K c U a 0 = 0 :=
  extensionPairing_eq_zero hi F K c (TensorProduct.tmul_zero _ a)

theorem extensionPairing_zero_left (U : Y.Cᵒᵖ) (m : F.val.obj U) :
    extensionPairing hi F K c U 0 m = 0 :=
  extensionPairing_eq_zero hi F K c (TensorProduct.zero_tmul _ m)

theorem extensionPairing_smul_left (U : Y.Cᵒᵖ)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf
      ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj.obj U)
    (a : hi.I.val.obj U) (m : F.val.obj U) :
    extensionPairing hi F K c U (r • a) m = r • extensionPairing hi F K c U a m :=
  extensionPairing_eq_smul hi F K c
    (TensorProduct.smul_tmul' (R := ((pushforwardCommRingFunctor i.toToposHom).obj X.O).obj.obj U)
      (R' := ((pushforwardCommRingFunctor i.toToposHom).obj X.O).obj.obj U) r a m).symm

theorem extensionPairing_smul_right (U : Y.Cᵒᵖ)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf
      ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj.obj U)
    (a : hi.I.val.obj U) (m : F.val.obj U) :
    extensionPairing hi F K c U a (r • m) = r • extensionPairing hi F K c U a m :=
  extensionPairing_eq_smul hi F K c
    (TensorProduct.tmul_smul (R := ((pushforwardCommRingFunctor i.toToposHom).obj X.O).obj.obj U)
      (R' := ((pushforwardCommRingFunctor i.toToposHom).obj X.O).obj.obj U) r a m)

theorem extensionPairing_naturality {U V : Y.Cᵒᵖ} (f : U ⟶ V) (a : hi.I.val.obj U)
    (m : F.val.obj U) :
    K.val.map f (extensionPairing hi F K c U a m) =
      extensionPairing hi F K c V (hi.I.val.map f a) (F.val.map f m) :=
  (PresheafOfModules.naturality_apply c.val f _).symm.trans
    (congrArg (c.val.app V)
      (PresheafOfModules.naturality_apply ((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf
          ((pushforwardCommRingFunctor i.toToposHom).obj X.O))
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf
          ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj)).unit.app
        (PresheafOfModules.tensorObj hi.I.val F.val)) f _).symm)

end Pairing

/-! ### The trivial extension `F'_{c,triv} = F ⊕ K` -/

section TrivialExtension

attribute [local implicit_reducible] SheafOfModules.unit PresheafOfModules.unit
  CategoryTheory.ConcreteCategory.hom CategoryTheory.sheafCompose SheafOfModules.forget
  SheafOfModules.restrictScalars PresheafOfModules.restrictScalars ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj' PresheafOfModules.restrictScalarsObj

variable [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
  (hi : FirstOrderThickening i) (π : Trivialization i)
  (F K : SheafOfModules.{w'}
    (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))
  (c : ((Stacks.SheafOfModules.Tensor.sheafTensor
    ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj hi.I).obj F ⟶ K)

/-- **The trivial extension** `F'_{c,triv}` of `F` by `K` attached to `c` and the trivialization
`π`: the sheaf `F ⊕ K` with the `O'`-module structure

    r · (m, k) = (q r · m, q r · k + c(d r ⊗ m)),

where `q : O' ⟶ O` is the structure map and `d r = r - π^♯(q r)` is the derivation of the
splitting `O' = O ⊕ I` given by `π`. -/
noncomputable def trivialExtensionModule :
    SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) :=
  Stacks.SheafOfModules.SplitSquareZero.extensionSheafModule
    (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
      Stacks.SheafOfModules.Tensor.ringSheaf
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
    (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp) hi.I F K
    (trivializationDerivation hi π) (extensionPairing hi F K c)
    (trivializationDerivation_zero hi π) (trivializationDerivation_one hi π)
    (trivializationDerivation_add hi π) (trivializationDerivation_mul hi π)
    (extensionPairing_add_left hi F K c) (extensionPairing_add_right hi F K c)
    (extensionPairing_smul_left hi F K c) (extensionPairing_smul_right hi F K c)
    (fun _ _ f r => trivializationDerivation_naturality hi π f r)
    (fun _ _ f a m => extensionPairing_naturality hi F K c f a m)

/-- The sections of the trivial extension over `U` are the pairs `F(U) × K(U)`, on which a
section `r` of `O'` acts by `r · (m, k) = (q r · m, q r · k + c(d r ⊗ m))`. -/
theorem trivialExtensionModule_smul (U : Y.Cᵒᵖ)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U)
    (z : (trivialExtensionModule hi π F K c).val.obj U) :
    r • z = (structureApp i U r • z.1, structureApp i U r • z.2 +
      extensionPairing hi F K c U (trivializationDerivation hi π U r) z.1) :=
  rfl

theorem trivialExtensionModule_smul_fst (U : Y.Cᵒᵖ)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U)
    (z : (trivialExtensionModule hi π F K c).val.obj U) :
    (r • z).1 = structureApp i U r • z.1 :=
  rfl

theorem trivialExtensionModule_smul_snd (U : Y.Cᵒᵖ)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U)
    (z : (trivialExtensionModule hi π F K c).val.obj U) :
    (r • z).2 = structureApp i U r • z.2 +
      extensionPairing hi F K c U (trivializationDerivation hi π U r) z.1 :=
  rfl

/-- The inclusion `K ⟶ F'_{c,triv}` of the second summand. -/
noncomputable def trivialExtensionInr :
    (SheafOfModules.restrictScalars
      (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
      Stacks.SheafOfModules.Tensor.ringSheaf
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
    (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj K ⟶
      trivialExtensionModule hi π F K c := by
  refine ⟨{
    app := fun U => ModuleCat.ofHom
      (X := ((SheafOfModules.restrictScalars
        (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
      Stacks.SheafOfModules.Tensor.ringSheaf
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
    (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj K).val.obj U)
      (Y := (trivialExtensionModule hi π F K c).val.obj U) {
        toFun := fun k => (0, k)
        map_add' := fun a b => Prod.ext (add_zero 0).symm rfl
        map_smul' := fun r k => ?_ }
    naturality := ?_ }⟩
  · refine (Prod.ext (smul_zero _).symm ?_).trans
      (trivialExtensionModule_smul hi π F K c U r _).symm
    change @HSMul.hSMul _ (K.val.obj U) (K.val.obj U) instHSMul (structureApp i U r) k =
      @HSMul.hSMul _ (K.val.obj U) (K.val.obj U) instHSMul (structureApp i U r) k +
        extensionPairing hi F K c U (trivializationDerivation hi π U r) 0
    rw [extensionPairing_zero_right, add_zero]
  · intro U V f
    ext k
    exact Prod.ext (F.val.map f).hom.map_zero.symm rfl

/-- The projection `F'_{c,triv} ⟶ F` onto the first summand. -/
noncomputable def trivialExtensionFst :
    trivialExtensionModule hi π F K c ⟶
      (SheafOfModules.restrictScalars
        (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
      Stacks.SheafOfModules.Tensor.ringSheaf
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
    (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj F :=
  ⟨{ app := fun U => ModuleCat.ofHom
        (X := (trivialExtensionModule hi π F K c).val.obj U)
        (Y := ((SheafOfModules.restrictScalars
          (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
      Stacks.SheafOfModules.Tensor.ringSheaf
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
    (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj F).val.obj U) {
          toFun := Prod.fst
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
     naturality := fun _ => rfl }⟩

theorem trivialExtensionInr_fst :
    trivialExtensionInr hi π F K c ≫ trivialExtensionFst hi π F K c = 0 := by
  ext U k
  rfl

theorem trivialExtensionInr_mono : Mono (trivialExtensionInr hi π F K c) := by
  constructor
  intro M a b h
  ext U x
  exact congrArg (fun f => ((f.val.app U).hom x).2) h

theorem trivialExtensionFst_epi : Epi (trivialExtensionFst hi π F K c) := by
  constructor
  intro M a b h
  ext U x
  exact congrArg (fun f => (f.val.app U).hom
    (x, 0)) h

/-- A map into the trivial extension killed by the projection factors through the inclusion. -/
noncomputable def trivialExtensionKernelLift
    {M : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)}
    (f : M ⟶ trivialExtensionModule hi π F K c)
    (hf : f ≫ trivialExtensionFst hi π F K c = 0) :
    M ⟶ (SheafOfModules.restrictScalars
      (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
      Stacks.SheafOfModules.Tensor.ringSheaf
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
    (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj K := by
  have hfst (U) (x : M.val.obj U) :
      ((f.val.app U).hom x).1 = 0 :=
    congrArg (fun g => (g.val.app U).hom x) hf
  refine ⟨{
    app := fun U => ModuleCat.ofHom
      (X := M.val.obj U)
      (Y := ((SheafOfModules.restrictScalars
        (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
      Stacks.SheafOfModules.Tensor.ringSheaf
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
    (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj K).val.obj U) {
        toFun := fun x => ((f.val.app U).hom x).2
        map_add' := fun x y => congrArg Prod.snd (map_add (f.val.app U).hom x y)
        map_smul' := ?_ }
    naturality := ?_ }⟩
  · intro r x
    have hmap := (map_smul (f.val.app U).hom r x).trans
      (trivialExtensionModule_smul hi π F K c U r ((f.val.app U).hom x))
    refine (congrArg Prod.snd hmap).trans ?_
    change structureApp i U r • _ + extensionPairing hi F K c U (trivializationDerivation hi π U r)
      ((f.val.app U).hom x).1 = _
    rw [hfst, extensionPairing_zero_right, add_zero]
    rfl
  · intro U V g
    ext x
    exact congrArg Prod.snd
      (PresheafOfModules.naturality_apply f.val g x)

theorem trivialExtensionKernelLift_inr
    {M : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)}
    (f : M ⟶ trivialExtensionModule hi π F K c)
    (hf : f ≫ trivialExtensionFst hi π F K c = 0) :
    trivialExtensionKernelLift hi π F K c f hf ≫ trivialExtensionInr hi π F K c = f := by
  ext U x
  exact Prod.ext (congrArg (fun g => (g.val.app U).hom x) hf).symm rfl

/-- The short complex `0 ⟶ K ⟶ F'_{c,triv} ⟶ F ⟶ 0` of the trivial extension. -/
noncomputable abbrev trivialExtensionShortComplex :
    ShortComplex (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :=
  ShortComplex.mk (trivialExtensionInr hi π F K c) (trivialExtensionFst hi π F K c)
    (trivialExtensionInr_fst hi π F K c)

/-- The trivial extension is a short exact sequence of `O'`-modules. -/
theorem trivialExtensionShortComplex_shortExact :
    (trivialExtensionShortComplex hi π F K c).ShortExact := by
  have : Mono (trivialExtensionInr hi π F K c) := trivialExtensionInr_mono hi π F K c
  have : Epi (trivialExtensionFst hi π F K c) := trivialExtensionFst_epi hi π F K c
  have hlim : IsLimit (KernelFork.ofι (trivialExtensionInr hi π F K c)
      (trivialExtensionShortComplex hi π F K c).zero) :=
    KernelFork.IsLimit.ofι _ _
      (fun f hf => trivialExtensionKernelLift hi π F K c f hf)
      (fun f hf => trivialExtensionKernelLift_inr hi π F K c f hf)
      (fun f hf m hm => (cancel_mono (trivialExtensionInr hi π F K c)).mp
        (hm.trans (trivialExtensionKernelLift_inr hi π F K c f hf).symm))
  exact ⟨(trivialExtensionShortComplex hi π F K c).exact_of_f_is_kernel hlim⟩

/-- The trivial extension `0 ⟶ K ⟶ F'_{c,triv} ⟶ F ⟶ 0`, as an extension in the sense of
Stacks 08MB. -/
noncomputable def trivialExtension :
    Abelian.YonedaExtension
      ((SheafOfModules.restrictScalars
        (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
      Stacks.SheafOfModules.Tensor.ringSheaf
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
    (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj F)
      ((SheafOfModules.restrictScalars
        (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
      Stacks.SheafOfModules.Tensor.ringSheaf
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
    (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj K) 0 :=
  Abelian.shortExactYonedaExtension (trivialExtensionShortComplex_shortExact hi π F K c)

/-- **The canonical map of the trivial extension is `c`**: `c_{F'_{c,triv}} = c`. A section `a` of
the ideal acts on `(m, k)` by `(q a · m, q a · k + c(d a ⊗ m)) = (0, c(a ⊗ m))`, because `q` kills
the ideal and `d` is the identity on it. -/
theorem trivialExtension_extensionActionMap
    [HasSheafify Y.J AddCommGrpCat.{w'}] :
    (extensionActionMap hi (trivialExtension hi π F K c)).1 = c := by
  refine extensionActionMap_unique hi _ c fun U a x => ?_
  refine Prod.ext ?_ ?_
  · refine Eq.trans ?_ (trivialExtensionModule_smul_fst hi π F K c U (idealSection hi U a) x).symm
    rw [structureApp_idealSection, zero_smul]
    rfl
  · refine Eq.trans ?_ (trivialExtensionModule_smul_snd hi π F K c U (idealSection hi U a) x).symm
    rw [structureApp_idealSection, zero_smul, zero_add, trivializationDerivation_idealSection]
    rfl

end TrivialExtension

/-! ### The class of the trivial extension -/

section TrivialExtensionClass

attribute [local implicit_reducible] SheafOfModules.unit PresheafOfModules.unit
  CategoryTheory.ConcreteCategory.hom CategoryTheory.sheafCompose SheafOfModules.forget
  SheafOfModules.restrictScalars PresheafOfModules.restrictScalars ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj' PresheafOfModules.restrictScalarsObj

variable [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
  [HasSheafify Y.J AddCommGrpCat.{w'}]
  (hi : FirstOrderThickening i) (π : Trivialization i)
  (F K : SheafOfModules.{w'}
    (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))
  (c : ((Stacks.SheafOfModules.Tensor.sheafTensor
    ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj hi.I).obj F ⟶ K)

/-- **The projection of the trivial extension onto its second summand, read along the
trivialization.** The projection `(m, k) ↦ k` is not `O'`-linear, but it is `O`-linear for the
action of `O` through the splitting `π^♯`, because the derivation kills the image of the
splitting. -/
noncomputable def restrictedTrivialExtensionSnd :
    (splitRestriction i hi π).obj (trivialExtensionModule hi π F K c) ⟶
      (splitRestriction i hi π).obj ((SheafOfModules.restrictScalars
        (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
      Stacks.SheafOfModules.Tensor.ringSheaf
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
    (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj K) :=
  ⟨{ app := fun U => ModuleCat.ofHom
        (X := ((splitRestriction i hi π).obj (trivialExtensionModule hi π F K c)).val.obj U)
        (Y := ((splitRestriction i hi π).obj ((SheafOfModules.restrictScalars
          (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
      Stacks.SheafOfModules.Tensor.ringSheaf
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
    (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj K)).val.obj U) {
          toFun := Prod.snd
          map_add' := fun _ _ => rfl
          map_smul' := fun a z => by
            refine (trivialExtensionModule_smul_snd hi π F K c U (splitApp hi π U a) z).trans ?_
            rw [trivializationDerivation_splitApp, extensionPairing_zero_left, add_zero]
            rfl }
     naturality := fun _ => rfl }⟩

/-- Read along the trivialization, the trivial extension splits: the projection onto the second
summand retracts the inclusion of `K`. -/
theorem splitExtension_trivialExtension_f_retraction :
    (splitExtension i hi π F K (trivialExtension hi π F K c)).f ≫
        (restrictedTrivialExtensionSnd hi π F K c ≫
          (splitRestrictionRestrictScalarsIso i hi π K).hom) = 𝟙 K := by
  have h : (splitRestriction i hi π).map (trivialExtension hi π F K c).f ≫
      restrictedTrivialExtensionSnd hi π F K c = 𝟙 _ := by
    ext U k
    rfl
  have h' : (splitRestriction i hi π).map (trivialExtension hi π F K c).f ≫
      (restrictedTrivialExtensionSnd hi π F K c ≫
        (splitRestrictionRestrictScalarsIso i hi π K).hom) =
        (splitRestrictionRestrictScalarsIso i hi π K).hom :=
    ((Category.assoc _ _ _).symm.trans
      (congrArg (fun g => g ≫ (splitRestrictionRestrictScalarsIso i hi π K).hom) h)).trans
      (Category.id_comp _)
  exact (Category.assoc (splitRestrictionRestrictScalarsIso i hi π K).inv
      ((splitRestriction i hi π).map (trivialExtension hi π F K c).f)
      (restrictedTrivialExtensionSnd hi π F K c ≫
        (splitRestrictionRestrictScalarsIso i hi π K).hom)).trans
    ((congrArg (fun g => (splitRestrictionRestrictScalarsIso i hi π K).inv ≫ g) h').trans
      (splitRestrictionRestrictScalarsIso i hi π K).inv_hom_id)

/-- **The trivial extension maps to the zero class**: `ξ_{F'_{c,triv}} = 0`. Read along the
trivialization it is a split short exact sequence, and a short exact sequence whose first map has
a retraction `ρ` has zero class, the class being killed by precomposition with that map. -/
theorem underlyingExtensionClass_trivialExtension
    [HasExt.{e} (SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))] :
    underlyingExtensionClass i hi π F K (trivialExtension hi π F K c) = 0 := by
  let S := splitExtension i hi π F K (trivialExtension hi π F K c)
  have hS : S.ShortExact := splitExtension_shortExact i hi π F K (trivialExtension hi π F K c)
  let ρ := restrictedTrivialExtensionSnd hi π F K c ≫
    (splitRestrictionRestrictScalarsIso i hi π K).hom
  have h : Abelian.Ext.mk₀ (𝟙 S.X₁) =
      (Abelian.Ext.mk₀ S.f).comp (Abelian.Ext.mk₀ ρ) (zero_add 0) :=
    ((Abelian.Ext.mk₀_comp_mk₀ S.f ρ).trans
      (congrArg Abelian.Ext.mk₀ (splitExtension_trivialExtension_f_retraction hi π F K c))).symm
  change hS.extClass = 0
  refine (Abelian.Ext.comp_mk₀_id hS.extClass).symm.trans ?_
  rw [h]
  exact hS.extClass_comp_assoc _

end TrivialExtensionClass

/-! ### The bijection with `Ext¹_O(F, K)` -/

section ExtensionClassBijection

attribute [local implicit_reducible] SheafOfModules.unit PresheafOfModules.unit
  CategoryTheory.ConcreteCategory.hom CategoryTheory.sheafCompose SheafOfModules.forget
  SheafOfModules.restrictScalars PresheafOfModules.restrictScalars ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj' PresheafOfModules.restrictScalarsObj
  Stacks.SheafOfModules.Tensor.ringSheaf

variable [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
  [HasSheafify Y.J AddCommGrpCat.{w'}]
  (hi : FirstOrderThickening i) (π : Trivialization i)
  (F K : SheafOfModules.{w'}
    (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))
  [HasExt.{e} (SheafOfModules.{w'}
    (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))]
  [HasExt.{e} (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]

omit [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
  [HasSheafify Y.J AddCommGrpCat.{w'}]
  [HasExt.{e} (SheafOfModules.{w'}
    (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))]
  [HasExt.{e} (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))] in
/-- Naturality of `splitRestrictionRestrictScalarsIso`: a map of `O`-modules restricted to `O'`
and read back along the splitting is the map itself. -/
theorem splitRestrictionRestrictScalarsIso_hom_naturality
    {M N : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O))}
    (φ : M ⟶ N) :
    (splitRestriction i hi π).map ((SheafOfModules.restrictScalars
        (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
      Stacks.SheafOfModules.Tensor.ringSheaf
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
    (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).map φ) ≫
        (splitRestrictionRestrictScalarsIso i hi π N).hom =
      (splitRestrictionRestrictScalarsIso i hi π M).hom ≫ φ := by
  ext U x
  rfl

/-- Reading a class of `Ext¹_{O'}(F, K)` along the trivialization: the homomorphism
`Ext¹_{O'}(F, K) ⟶ Ext¹_O(F, K)` induced by the exact functor `splitRestriction`, with the outer
terms identified with `F` and `K` by `splitRestrictionRestrictScalarsIso`. On the class of an
extension `F'` it is `ξ_{F'}` (`underlyingExtensionClass_eq_splitRestrictionExtHom`). -/
noncomputable def splitRestrictionExtHom :
    Abelian.Ext ((SheafOfModules.restrictScalars
        (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
      Stacks.SheafOfModules.Tensor.ringSheaf
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
    (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj F)
      ((SheafOfModules.restrictScalars
        (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
      Stacks.SheafOfModules.Tensor.ringSheaf
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
    (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj K) 1 →+
      Abelian.Ext F K 1 :=
  AddMonoidHom.mk'
    (fun ξ => (Abelian.Ext.mk₀ (splitRestrictionRestrictScalarsIso i hi π F).inv).comp
      ((ξ.mapExactFunctor (splitRestriction i hi π)).comp
        (Abelian.Ext.mk₀ (splitRestrictionRestrictScalarsIso i hi π K).hom) (add_zero 1))
      (zero_add 1))
    (fun ξ₁ ξ₂ => by
      rw [Abelian.Ext.mapExactFunctor_add, Abelian.Ext.add_comp, Abelian.Ext.comp_add])

/-- The value of `splitRestrictionExtHom` on the class of a short exact sequence of
`O'`-modules which, read along the trivialization, maps to a short exact sequence of `O`-modules
by the identifications of the outer terms: the two classes agree. -/
theorem splitRestrictionExtHom_extClass_of_hom
    {H : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)}
    {a : (SheafOfModules.restrictScalars
      (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
      Stacks.SheafOfModules.Tensor.ringSheaf
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
    (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj K ⟶ H}
    {b : H ⟶ (SheafOfModules.restrictScalars
      (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
      Stacks.SheafOfModules.Tensor.ringSheaf
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
    (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj F} {w : a ≫ b = 0}
    (hT : (ShortComplex.mk a b w).ShortExact)
    {N : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O))}
    {f : K ⟶ N} {g : N ⟶ F} {w' : f ≫ g = 0}
    (hS : (ShortComplex.mk f g w').ShortExact) (v : (splitRestriction i hi π).obj H ⟶ N)
    (hv : (splitRestriction i hi π).map a ≫ v =
      (splitRestrictionRestrictScalarsIso i hi π K).hom ≫ f)
    (hv' : v ≫ g =
      (splitRestriction i hi π).map b ≫ (splitRestrictionRestrictScalarsIso i hi π F).hom) :
    splitRestrictionExtHom hi π F K hT.extClass = hS.extClass := by
  have hnat := ShortComplex.ShortExact.extClass_naturality
    (hT.map_of_exact (splitRestriction i hi π)) hS
    { τ₁ := (splitRestrictionRestrictScalarsIso i hi π K).hom
      τ₂ := v
      τ₃ := (splitRestrictionRestrictScalarsIso i hi π F).hom
      comm₁₂ := hv.symm
      comm₂₃ := hv' }
  change (Abelian.Ext.mk₀ (splitRestrictionRestrictScalarsIso i hi π F).inv).comp
      ((hT.extClass.mapExactFunctor (splitRestriction i hi π)).comp
        (Abelian.Ext.mk₀ (splitRestrictionRestrictScalarsIso i hi π K).hom) (add_zero 1))
      (zero_add 1) = hS.extClass
  rw [Abelian.Ext.mapExactFunctor_extClass, hnat, Abelian.Ext.mk₀_comp_mk₀_assoc,
    Iso.inv_hom_id, Abelian.Ext.mk₀_id_comp]

/-- **The map `F' ↦ ξ_{F'}` factors through the class of `F'`.** The class
`ξ_{F'} ∈ Ext¹_O(F, K)` of an extension over the thickening is the image of its class in
`Ext¹_{O'}(F, K)` under `splitRestrictionExtHom`; in particular it only depends on the
isomorphism class of the extension. -/
theorem underlyingExtensionClass_eq_splitRestrictionExtHom
    (E : Abelian.YonedaExtension
      ((SheafOfModules.restrictScalars
        (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
      Stacks.SheafOfModules.Tensor.ringSheaf
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
    (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj F)
      ((SheafOfModules.restrictScalars
        (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
      Stacks.SheafOfModules.Tensor.ringSheaf
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
    (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj K) 0) :
    underlyingExtensionClass i hi π F K E =
      splitRestrictionExtHom hi π F K (extensionClass F K E) :=
  (splitRestrictionExtHom_extClass_of_hom hi π F K (yonedaExtension_shortExact E)
    (splitExtension_shortExact i hi π F K E) (𝟙 _)
    (by rw [Category.comp_id]; exact (Iso.hom_inv_id_assoc _ _).symm)
    (Category.id_comp _)).symm

/-- `splitRestrictionExtHom` undoes the restriction of scalars along the structure map: reading a
class of `Ext¹_O(F, K)` as a class over the thickening and back along the splitting returns it,
because the splitting is a section of the structure map. -/
theorem splitRestrictionExtHom_mapExtAddHom (x : Abelian.Ext F K 1) :
    splitRestrictionExtHom hi π F K ((SheafOfModules.restrictScalars
      (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
      Stacks.SheafOfModules.Tensor.ringSheaf
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
    (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).mapExtAddHom F K 1 x) =
      x := by
  obtain ⟨N, f, g, w₀, h₀, hx⟩ :=
    (Abelian.Ext.extClass_surjective_and_eq_iff_iso_and_baerSum _ F K).1 x
  subst hx
  rw [Functor.mapExtAddHom_apply, Abelian.Ext.mapExactFunctor_extClass]
  exact splitRestrictionExtHom_extClass_of_hom hi π F K
    (h₀.map_of_exact (SheafOfModules.restrictScalars
      (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
      Stacks.SheafOfModules.Tensor.ringSheaf
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
    (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp))) h₀
    (splitRestrictionRestrictScalarsIso i hi π N).hom
    (splitRestrictionRestrictScalarsIso_hom_naturality hi π f)
    (splitRestrictionRestrictScalarsIso_hom_naturality hi π g).symm

end ExtensionClassBijection

/-! ### Stacks 08MI -/

section Remark

attribute [local implicit_reducible] SheafOfModules.unit PresheafOfModules.unit
  CategoryTheory.ConcreteCategory.hom CategoryTheory.sheafCompose SheafOfModules.forget
  SheafOfModules.restrictScalars PresheafOfModules.restrictScalars ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj' PresheafOfModules.restrictScalarsObj
  Stacks.SheafOfModules.Tensor.ringSheaf

variable [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
  [HasSheafify Y.J AddCommGrpCat.{w'}]
  (hi : FirstOrderThickening i) (π : Trivialization i)
  (F K : SheafOfModules.{w'}
    (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))
  [HasExt.{e} (SheafOfModules.{w'}
    (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))]
  [HasExt.{e} (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]

/-- **Stacks 08MI.** Let `i : (Sh(C), O) ⟶ (Sh(D), O')` be a first order thickening of ringed
topoi with square-zero ideal `I`, and `π` a trivialization of it. Let `F`, `K` be `O`-modules and
`c : I ⊗_O F ⟶ K` a map.

* The trivial extension `F'_{c,triv} = F ⊕ K` (`trivialExtensionModule`, `trivialExtension`)
  carries the `O'`-module structure `r · (m, k) = (q r · m, q r · k + c(d r ⊗ m))` built from
  the splitting `O' = O ⊕ I` of `π` and from `c`, and it is an extension
  `0 ⟶ K ⟶ F'_{c,triv} ⟶ F ⟶ 0` as in Stacks 08MB with `c_{F'_{c,triv}} = c`.
* The class `ξ_{F'} ∈ Ext¹_O(F, K)` of an extension `F'`, obtained by reading `F'` as an
  `O`-module through `π^♯` (`underlyingExtensionClass`), only depends on the class of `F'`
  (through `splitRestrictionExtHom`), and `F' ↦ ξ_{F'}` is a bijection from the isomorphism
  classes of extensions with `c_{F'} = c` onto `Ext¹_O(F, K)`. The isomorphism classes are
  represented by their classes in `Ext¹_{O'}(F, K)` (`FixedActionExtensionClass`); the bijection is
  also stated on extensions: every class is `ξ_{F'}` of an extension with `c_{F'} = c`, and two
  such extensions with the same `ξ` are isomorphic as extensions.
* The trivial extension maps to the zero class. -/
@[stacks 08MI]
theorem trivialExtension_bijective_underlyingExtensionClass
    (c : ((Stacks.SheafOfModules.Tensor.sheafTensor
      ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj hi.I).obj F ⟶ K) :
    (∀ (U : Y.Cᵒᵖ) (r : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U)
        (z : (trivialExtensionModule hi π F K c).val.obj U),
        r • z = (structureApp i U r • z.1, structureApp i U r • z.2 +
          extensionPairing hi F K c U (trivializationDerivation hi π U r) z.1)) ∧
      (extensionActionMap hi (trivialExtension hi π F K c)).1 = c ∧
      (∀ E : Abelian.YonedaExtension
          ((SheafOfModules.restrictScalars
            (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
      Stacks.SheafOfModules.Tensor.ringSheaf
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
    (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj F)
          ((SheafOfModules.restrictScalars
            (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
      Stacks.SheafOfModules.Tensor.ringSheaf
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
    (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj K) 0,
        underlyingExtensionClass i hi π F K E =
          splitRestrictionExtHom hi π F K (extensionClass F K E)) ∧
      Function.Bijective (fun ξ : FixedActionExtensionClass.{_, _, _, _, _, _, e} hi F K c =>
        splitRestrictionExtHom hi π F K ξ.1) ∧
      (∀ η : Abelian.Ext F K 1, ∃ E : Abelian.YonedaExtension
          ((SheafOfModules.restrictScalars
            (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
      Stacks.SheafOfModules.Tensor.ringSheaf
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
    (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj F)
          ((SheafOfModules.restrictScalars
            (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
      Stacks.SheafOfModules.Tensor.ringSheaf
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
    (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj K) 0,
        (extensionActionMap hi E).1 = c ∧ underlyingExtensionClass i hi π F K E = η) ∧
      (∀ E E' : Abelian.YonedaExtension
          ((SheafOfModules.restrictScalars
            (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
      Stacks.SheafOfModules.Tensor.ringSheaf
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
    (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj F)
          ((SheafOfModules.restrictScalars
            (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
      Stacks.SheafOfModules.Tensor.ringSheaf
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
    (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj K) 0,
        (extensionActionMap hi E).1 = c → (extensionActionMap hi E').1 = c →
        underlyingExtensionClass i hi π F K E = underlyingExtensionClass i hi π F K E' →
        ∃ φ : E.Z.left ≅ E'.Z.left, E.f ≫ φ.hom = E'.f ∧ φ.hom ≫ E'.g = E.g) ∧
      underlyingExtensionClass i hi π F K (trivialExtension hi π F K c) = 0 := by
  let R := SheafOfModules.restrictScalars.{w'}
    (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
      Stacks.SheafOfModules.Tensor.ringSheaf
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
    (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)
  let Φ := splitRestrictionExtHom hi π F K
  have hfac (E) : underlyingExtensionClass i hi π F K E = Φ (extensionClass F K E) :=
    underlyingExtensionClass_eq_splitRestrictionExtHom hi π F K E
  have hact := trivialExtension_extensionActionMap hi π F K c
  have htriv := underlyingExtensionClass_trivialExtension.{e} hi π F K c
  have hinj : Function.Injective
      (fun ξ : FixedActionExtensionClass.{_, _, _, _, _, _, e} hi F K c => Φ ξ.1) := by
    rintro ⟨x₁, hx₁⟩ ⟨x₂, hx₂⟩ h
    change Φ x₁ = Φ x₂ at h
    obtain ⟨a, ha⟩ := (exists_extensionActionMap_eq_iff_exists_add_mapExtAddHom hi ⟨x₁, hx₁⟩ x₂).1
      hx₂
    change x₁ + R.mapExtAddHom F K 1 a = x₂ at ha
    subst ha
    have h' : Φ (x₁ + R.mapExtAddHom F K 1 a) = Φ x₁ + a := by
      rw [map_add, splitRestrictionExtHom_mapExtAddHom]
    have ha0 : a = 0 := by
      have hsub : a = (Φ x₁ + a) - Φ x₁ := by abel
      rw [hsub, ← h']
      exact sub_eq_zero_of_eq h.symm
    subst ha0
    have hx : x₁ = x₁ + R.mapExtAddHom F K 1 0 := by rw [map_zero, add_zero]
    exact Subtype.ext hx
  have hsurj : Function.Surjective
      (fun ξ : FixedActionExtensionClass.{_, _, _, _, _, _, e} hi F K c => Φ ξ.1) := by
    intro η
    let b : FixedActionExtensionClass.{_, _, _, _, _, _, e} hi F K c :=
      ⟨extensionClass F K (trivialExtension hi π F K c), trivialExtension hi π F K c, hact, rfl⟩
    refine ⟨⟨b.1 + R.mapExtAddHom F K 1 η,
      (exists_extensionActionMap_eq_iff_exists_add_mapExtAddHom hi b _).2 ⟨η, rfl⟩⟩, ?_⟩
    change Φ (b.1 + R.mapExtAddHom F K 1 η) = η
    rw [map_add, splitRestrictionExtHom_mapExtAddHom]
    change Φ (extensionClass F K (trivialExtension hi π F K c)) + η = η
    rw [← hfac]
    exact (congrArg (· + η) htriv).trans (zero_add η)
  refine ⟨trivialExtensionModule_smul hi π F K c, hact, hfac, ⟨hinj, hsurj⟩, ?_, ?_, htriv⟩
  · intro η
    obtain ⟨⟨x, E, hE, hx⟩, hη⟩ := hsurj η
    refine ⟨E, hE, ?_⟩
    rw [hfac, hx]
    exact hη
  · intro E E' hE hE' h
    have hcl : extensionClass F K E = extensionClass F K E' := by
      have := hinj (a₁ := ⟨extensionClass F K E, E, hE, rfl⟩)
        (a₂ := ⟨extensionClass F K E', E', hE', rfl⟩) (by
          change Φ (extensionClass F K E) = Φ (extensionClass F K E')
          rw [← hfac, ← hfac]
          exact h)
      exact congrArg Subtype.val this
    exact ((Abelian.Ext.extClass_surjective_and_eq_iff_iso_and_baerSum
      (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (R.obj F) (R.obj K)).2.1
      E.Z.left E'.Z.left E.f E.g _ E'.f E'.g _
      (yonedaExtension_shortExact E) (yonedaExtension_shortExact E')).1 hcl

end Remark

end Deformation.ToposThickening

end
