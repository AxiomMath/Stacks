module

public import StacksFrontier.AlgebraicGeometry.Descent.Module.Amitsur
public import StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModuleAffineBaseChange

/-!
# The affine base-change comparison of the associated module is natural

Let `S` be a scheme, `F` a quasi-coherent `𝒪_S`-module, `C` a site of schemes over `S`
presented by `toOver : C ⥤ Over S`, and `Fᵃ` the associated module of [Stacks, Tag 03DU]
(`Stacks.Sites.associatedPresheaf`).  Fix an object `T` of the site and write
`R = Γ(T, 𝒪)`, `M = Fᵃ(T)`.  For every object `Z` of `Over T` there is a comparison map

`Γ(Z, 𝒪) ⊗_R M ⟶ Fᵃ(Z)`,  `a ⊗ m ↦ a • m|_Z`,

and this file proves the two things about it that [Stacks, Tag 03FJ] needs and that
`StacksFrontier/AlgebraicGeometry/Topologies/AssociatedModuleAffineBaseChange.lean` does not
supply:

* it is **natural in `Z`**, on all of `(Over T)ᵒᵖ`;
* it is an **isomorphism when `Z` has affine total space**.

`Stacks.Sites.affineAssociatedBaseChangeIso` is the isomorphism at one fixed morphism, with no
naturality; but the Čech comparison of Tag 03FJ identifies two *cosimplicial* objects, so it
needs the comparison as a morphism of functors.  The naturality costs nothing beyond
`Stacks.Sites.associatedPresheaf_map_smul` and functoriality of `Fᵃ`, because the comparison is
given by the same formula `a ⊗ m ↦ a • m|_Z` at *every* object of `Over T`; only the
isomorphism clause needs affineness.

**That split is essential and not an artefact.**  The comparison is genuinely not an
isomorphism at a non-affine object: for `R = k[x, y]`, `T = Spec R`, `F` the module of
`M = R/(x, y)` and `Z = 𝔸² ∖ {0}` one has `Γ(Z, 𝒪) = R`, so `Γ(Z, 𝒪) ⊗_R M = M = k`, while the
pullback of `F` to `Z` is a skyscraper at the origin — a point not in `Z` — so `Fᵃ(Z) = 0`.  A
coefficient hypothesis of Tag 03FJ asking for the comparison on the whole slice is therefore
unavailable; the usable form asks for it only at the fibre powers of an affine over an affine,
which are affine.  See
`Stacks.Descent.cechCosimplicialObjectIsoAmitsurOfPowerSections`.

## Main definitions

* `Stacks.Sites.gammaUnder` and `Stacks.Sites.gammaAlg`: the coordinate rings of the objects of
  `Over T`, as rings under `Γ(T, 𝒪)` and as algebras over its universe lift — the base ring of
  `AlgebraicTopology.algebraMapArrow`, hence of the Amitsur complex.
* `Stacks.Sites.coeffFunctor`: the coefficient functor `A ↦ A ⊗_R M` of the Amitsur side, read
  as a functor to abelian groups.
* `Stacks.Sites.tensorToSections`: **the comparison**, as a morphism of functors on
  `(Over T)ᵒᵖ`.
* `Stacks.Sites.uliftBaseTensorAddEquiv`: `A ⊗_{ULift R} M ≃+ A ⊗_R M`.
* `Stacks.Sites.affineBaseChangeIsoOfEq`: the affine base-change comparison of
  [Stacks, Tag 02KH] in degree zero, with the ring map it extends scalars along taken as a
  parameter equal to `q.appLE ⊤ ⊤`.

## Main results

* `Stacks.Sites.tensorToSectionsApp_naturality`: **the naturality**, on generators.
* `Stacks.Sites.isIso_tensorToSectionsApp`: **the comparison is an isomorphism at an object
  with affine total space.**
* `Stacks.Sites.coeffRestrict_smul` and `Stacks.Sites.coeffMap_smul`: the semilinearity of the
  restriction maps of `Fᵃ`, in the two spellings the comparison needs.
* `Stacks.Sites.gammaMap_eq_appLE_top_top`: `Scheme.Γ.map f.op` and `f.appLE ⊤ ⊤` agree, which
  is the coherence between the coordinate algebra and the affine base-change comparison.

## Implementation notes

The coefficient functor lands in `AddCommGrpCat` rather than in `ModuleCat R`: the values of
`Fᵃ` are modules over *varying* coordinate rings, and only their underlying abelian groups form
a presheaf on the site.  `Stacks.Descent.amitsurCoefficients` is `ModuleCat R`-valued, so the
two differ by `CategoryTheory.forget₂`; relating the Čech complexes of the two is a separate
transport and is not done here.

Three spellings of the same ring have to be kept apart, and each has its own instance:
`Γ(-, ⊤)`, `AlgebraicGeometry.Scheme.Γ.obj (op -)`, and the carrier of the `CommAlgCat`
produced by `Stacks.Sites.gammaAlg`.  They are definitionally equal — `gammaAlg_obj_carrier` is
`rfl` — but instance search does not unfold `Scheme.Γ` or `gammaAlg`, so
`Stacks.Sites.instModuleCoeff`, `Stacks.Sites.instModuleCoeffSections` and
`Stacks.Sites.instModuleGammaAlg` register the same module structure three times, and the
affineness proof inserts one `inferInstanceAs` to move the `ULift R`-action from the `gammaAlg`
spelling to the `Γ(-, ⊤)` one.

`Stacks.Sites.affineBaseChangeIsoOfEq` is stated for a bare morphism of schemes and an
arbitrary quasi-coherent module, not for `g.left` and the pullback of `F` along `T.hom`.  That
is not generality for its own sake: the transport `subst hφ` has to check a defeq between the
two `CategoryTheory.ModuleCat.extendScalars` carriers, and at the specialized terms that check
exhausts the default recursion depth, which the general statement avoids.  For the same reason
the final generator computation is a term-level chain of `congrArg` and `map_smul` rather than
a `rw`: the rewrite patterns do not match, the `Semiring Γ(W, ⊤)` instance reached through
`CommRingCat` and the one reached through `ModuleCat.restrictScalars` being different terms.

## References

* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03FJ](https://stacks.math.columbia.edu/tag/03FJ)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicTopology
open scoped TensorProduct ChangeOfRings

universe u

namespace Stacks.Sites

variable (S : Scheme.{u}) (F : S.Modules) [F.IsQuasicoherent]
  {C : Type (u + 1)} [Category.{u} C] (toOver : C ⥤ Over S) (T : C)

/-! ### The coordinate algebras of the objects over a fixed object -/

/-- The universe-lift isomorphism of a commutative ring, as a morphism of `CommRingCat`. -/
public def uliftHom (R : CommRingCat.{u}) : CommRingCat.of (ULift.{u} R) ⟶ R :=
  CommRingCat.ofHom (ULift.ringEquiv (R := R)).toRingHom

/-- The coordinate rings of the objects of `Over T`, as rings under the coordinate ring of the
scheme underlying `T`. -/
public def gammaUnder : (Over T)ᵒᵖ ⥤ Under (Scheme.Γ.obj (op (toOver.obj T).left)) :=
  (Over.post (toOver ⋙ Over.forget S)).op ⋙
    (Under.opEquivOpOver ((toOver ⋙ Over.forget S).obj T)).inverse ⋙
      Under.post Scheme.Γ

/-- **The coordinate algebras of the objects over `T`.**  The object `Z` of `Over T` is sent to
`Γ(Z, 𝒪)`, regarded as an algebra over the universe lift of `Γ(T, 𝒪)` — which is the base ring
of `AlgebraicTopology.algebraMapArrow`, hence of the Amitsur complex. -/
public def gammaAlg :
    (Over T)ᵒᵖ ⥤ CommAlgCat.{u} (ULift.{u} (Scheme.Γ.obj (op (toOver.obj T).left))) :=
  gammaUnder S toOver T ⋙ Under.map (uliftHom (Scheme.Γ.obj (op (toOver.obj T).left))) ⋙
    (commAlgCatEquivUnder
      (CommRingCat.of (ULift.{u} (Scheme.Γ.obj (op (toOver.obj T).left))))).inverse

/-- The carrier of `Stacks.Sites.gammaAlg` at an object of `Over T` is its coordinate ring:
only the base ring is universe-lifted. -/
public theorem gammaAlg_obj_carrier (Z : Over T) :
    ((gammaAlg S toOver T).obj (op Z) : Type u) = Γ((toOver.obj Z.left).left, ⊤) :=
  rfl

/-- The structure map of `Stacks.Sites.gammaAlg` at an object of `Over T` is the coordinate
ring map of its structure morphism, read through the universe-lift equivalence of the base. -/
public theorem gammaAlg_algebraMap (Z : Over T)
    (x : ULift.{u} (Scheme.Γ.obj (op (toOver.obj T).left))) :
    algebraMap (ULift.{u} (Scheme.Γ.obj (op (toOver.obj T).left)))
        ((gammaAlg S toOver T).obj (op Z)) x =
      (Scheme.Γ.map ((toOver ⋙ Over.forget S).map Z.hom).op).hom (ULift.ringEquiv x) :=
  rfl

/-! ### The coefficient comparison -/

/-- The coefficient module of the Amitsur side: the sections of `Fᵃ` over `T`. -/
public abbrev coeffModule : Type u := (associatedPresheaf S F toOver).obj (op T)

/-- The base ring of the Amitsur side: the coordinate ring of the scheme underlying `T`,
spelled as `Stacks.Sites.gammaAlg` spells it. -/
public abbrev coeffBase : Type u := Scheme.Γ.obj (op (toOver.obj T).left)

/-- The sections of `Fᵃ` over an object of the site are a module over its coordinate ring, in
the `AlgebraicGeometry.Scheme.Γ` spelling. -/
public instance instModuleCoeff (X : C) :
    Module (Scheme.Γ.obj (op (toOver.obj X).left) : Type u)
      ((associatedPresheaf S F toOver).obj (op X) : Type u) :=
  associatedPresheafModule S F toOver (op X)

/-- The sections of `Fᵃ` over an object of the site are a module over its coordinate ring, in
the `Γ(-, ⊤)` spelling, which is the one `Stacks.Sites.affineAssociatedBaseChangeIso` uses. -/
public instance instModuleCoeffSections (X : C) :
    Module (Γ((toOver.obj X).left, ⊤) : Type u)
      ((associatedPresheaf S F toOver).obj (op X) : Type u) :=
  associatedPresheafModule S F toOver (op X)

/-- The sections of `Fᵃ` over an object of `Over T` are a module over its coordinate algebra. -/
public instance instModuleGammaAlg (Z : (Over T)ᵒᵖ) :
    Module (((gammaAlg S toOver T).obj Z : CommAlgCat.{u} _) : Type u)
      ((associatedPresheaf S F toOver).obj (op Z.unop.left) : Type u) :=
  associatedPresheafModule S F toOver (op Z.unop.left)

/-- **The coefficient functor of the Amitsur side, as a functor to abelian groups.**  Tensoring
a coordinate algebra with the coefficient module over the base ring.  This is
`Stacks.Descent.amitsurCoefficients` followed by the forgetful functor to abelian groups, which
is the shape in which the comparison below can be stated: the values of `Fᵃ` are modules over
*varying* coordinate rings, so only their underlying abelian groups form a presheaf. -/
public abbrev coeffFunctor :
    CommAlgCat.{u} (ULift.{u} (coeffBase S toOver T)) ⥤ AddCommGrpCat.{u} :=
  tensorModuleFunctor (ULift.{u} (coeffBase S toOver T)) (coeffModule S F toOver T) ⋙
    ModuleCat.restrictScalars
        (algebraMap (coeffBase S toOver T) (ULift.{u} (coeffBase S toOver T))) ⋙
      forget₂ (ModuleCat.{u} (coeffBase S toOver T)) AddCommGrpCat.{u}

/-- Restriction of a section of `Fᵃ` over `T` to an object of `Over T`. -/
public abbrev coeffRestrict (Z : (Over T)ᵒᵖ) :
    (associatedPresheaf S F toOver).obj (op T) ⟶
      (associatedPresheaf S F toOver).obj (op Z.unop.left) :=
  (associatedPresheaf S F toOver).map Z.unop.hom.op

/-- Restriction is semilinear over the base ring, which acts on the sections at `Z` through the
coordinate algebra of `Z`.  This is `Stacks.Sites.associatedPresheaf_map_smul` with the scalar
read in the spelling `Stacks.Sites.gammaAlg` uses. -/
public theorem coeffRestrict_smul (Z : (Over T)ᵒᵖ) (c : ULift.{u} (coeffBase S toOver T))
    (m : coeffModule S F toOver T) :
    coeffRestrict S F toOver T Z (c • m) =
      algebraMap (ULift.{u} (coeffBase S toOver T))
          (((gammaAlg S toOver T).obj Z : CommAlgCat.{u} _) : Type u) c •
        coeffRestrict S F toOver T Z m :=
  associatedPresheaf_map_smul S F toOver Z.unop.hom.op c.down m

/-- The restriction maps of `Fᵃ` are semilinear for the coordinate-algebra actions. -/
public theorem coeffMap_smul {Z Z' : (Over T)ᵒᵖ} (g : Z ⟶ Z')
    (a : (((gammaAlg S toOver T).obj Z : CommAlgCat.{u} _) : Type u))
    (x : ((associatedPresheaf S F toOver).obj (op Z.unop.left) : Type u)) :
    (associatedPresheaf S F toOver).map g.unop.left.op (a • x) =
      (gammaAlg S toOver T).map g a •
        (associatedPresheaf S F toOver).map g.unop.left.op x :=
  associatedPresheaf_map_smul S F toOver g.unop.left.op a x

/-- The bilinear data of the coefficient comparison: `(a, m) ↦ a • m|_Z`. -/
public def coeffBilin (Z : (Over T)ᵒᵖ) :
    (((gammaAlg S toOver T).obj Z : CommAlgCat.{u} _) : Type u) →+
      (coeffModule S F toOver T →+
        ((associatedPresheaf S F toOver).obj (op Z.unop.left) : Type u)) where
  toFun a :=
    { toFun := fun m => a • coeffRestrict S F toOver T Z m
      map_zero' := by simp only [map_zero, smul_zero]
      map_add' := fun x y => by simp only [map_add, smul_add] }
  map_zero' := AddMonoidHom.ext fun m => zero_smul _ _
  map_add' a b := AddMonoidHom.ext fun m => add_smul _ _ _

/-- The bilinear data is balanced over the base ring, so it descends to the tensor product. -/
public theorem coeffBilin_balanced (Z : (Over T)ᵒᵖ) (c : ULift.{u} (coeffBase S toOver T))
    (a : (((gammaAlg S toOver T).obj Z : CommAlgCat.{u} _) : Type u))
    (m : coeffModule S F toOver T) :
    coeffBilin S F toOver T Z (c • a) m = coeffBilin S F toOver T Z a (c • m) := by
  change (c • a) • coeffRestrict S F toOver T Z m =
    a • coeffRestrict S F toOver T Z (c • m)
  rw [coeffRestrict_smul, Algebra.smul_def, smul_smul, mul_comm]

/-- Two additive maps out of a tensor product agree as soon as they agree on the generators. -/
public theorem addHom_ext_tmul {Rr Mm : Type u} {Nn Pp : Type*} [CommRing Rr]
    [AddCommGroup Mm] [Module Rr Mm] [AddCommGroup Nn] [Module Rr Nn] [AddCommGroup Pp]
    {f h : Mm ⊗[Rr] Nn →+ Pp} (hfh : ∀ a m, f (a ⊗ₜ[Rr] m) = h (a ⊗ₜ[Rr] m)) : f = h := by
  refine AddMonoidHom.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a m => exact hfh a m
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- The component of the coefficient comparison at one object of `Over T`. -/
public def tensorToSectionsApp (Z : (Over T)ᵒᵖ) :
    (gammaAlg S toOver T ⋙ coeffFunctor S F toOver T).obj Z ⟶
      ((Over.forget T).op ⋙ associatedPresheaf S F toOver).obj Z :=
  AddCommGrpCat.ofHom (TensorProduct.liftAddHom (coeffBilin S F toOver T Z)
    (coeffBilin_balanced S F toOver T Z))

/-- The comparison sends the generator `a ⊗ m` to `a • m|_Z`. -/
public theorem tensorToSectionsApp_tmul (Z : (Over T)ᵒᵖ)
    (a : (((gammaAlg S toOver T).obj Z : CommAlgCat.{u} _) : Type u))
    (m : coeffModule S F toOver T) :
    tensorToSectionsApp S F toOver T Z (a ⊗ₜ[ULift.{u} (coeffBase S toOver T)] m) =
      a • coeffRestrict S F toOver T Z m :=
  rfl

/-- The structure maps of the source of the comparison act on the first tensor factor only. -/
public theorem coeffFunctor_map_tmul {Z Z' : (Over T)ᵒᵖ} (g : Z ⟶ Z')
    (a : (((gammaAlg S toOver T).obj Z : CommAlgCat.{u} _) : Type u))
    (m : coeffModule S F toOver T) :
    (gammaAlg S toOver T ⋙ coeffFunctor S F toOver T).map g
        (a ⊗ₜ[ULift.{u} (coeffBase S toOver T)] m) =
      (gammaAlg S toOver T).map g a ⊗ₜ[ULift.{u} (coeffBase S toOver T)] m :=
  rfl

/-- **Naturality of the coefficient comparison, on generators.**  Stated with the tensor
product spelled out, so that the rewrites act on a type-correct goal: the additive structure
`AddCommGrpCat` puts on the value of the composite functor and the one the tensor product
carries are definitionally but not syntactically equal. -/
public theorem tensorToSectionsApp_naturality {Z Z' : (Over T)ᵒᵖ} (g : Z ⟶ Z')
    (a : (((gammaAlg S toOver T).obj Z : CommAlgCat.{u} _) : Type u))
    (m : coeffModule S F toOver T) :
    tensorToSectionsApp S F toOver T Z'
        ((gammaAlg S toOver T).map g a ⊗ₜ[ULift.{u} (coeffBase S toOver T)] m) =
      (associatedPresheaf S F toOver).map g.unop.left.op
        (tensorToSectionsApp S F toOver T Z (a ⊗ₜ[ULift.{u} (coeffBase S toOver T)] m)) := by
  rw [tensorToSectionsApp_tmul, tensorToSectionsApp_tmul, coeffMap_smul]
  congr 1
  simp only [coeffRestrict, ← ConcreteCategory.comp_apply,
    ← (associatedPresheaf S F toOver).map_comp, ← op_comp, Over.w g.unop]

/-- **The coefficient comparison, on all of `(Over T)ᵒᵖ`.**  The map `a ⊗ m ↦ a • m|_Z` from the
tensor product of the coordinate algebra of `Z` with the sections of `Fᵃ` over `T` to the
sections of `Fᵃ` over `Z`.

**This is the naturality that `Stacks.Sites.affineAssociatedBaseChangeIso` does not have.**  That
isomorphism is pointwise at one morphism `g`, and the Čech comparison of [Stacks, Tag 03FJ]
needs the comparison as a morphism of cosimplicial objects, hence natural in the object.  The
naturality costs nothing beyond `Stacks.Sites.associatedPresheaf_map_smul` and functoriality of
`Fᵃ`, because the comparison is defined by the formula `a ⊗ m ↦ a • m|_Z` on *every* object;
only the statement that it is an isomorphism needs the object to have affine total space. -/
public def tensorToSections :
    gammaAlg S toOver T ⋙ coeffFunctor S F toOver T ⟶
      (Over.forget T).op ⋙ associatedPresheaf S F toOver where
  app Z := tensorToSectionsApp S F toOver T Z
  naturality Z Z' g := by
    apply AddCommGrpCat.hom_ext
    refine addHom_ext_tmul (Rr := ULift.{u} (coeffBase S toOver T))
      (Mm := (((gammaAlg S toOver T).obj Z : CommAlgCat.{u} _) : Type u))
      (Nn := coeffModule S F toOver T)
      (Pp := ((associatedPresheaf S F toOver).obj (op Z'.unop.left) : Type u))
      (fun a m => ?_)
    exact (congrArg (fun y => tensorToSectionsApp S F toOver T Z' y)
        (coeffFunctor_map_tmul S F toOver T g a m)).trans
      (tensorToSectionsApp_naturality S F toOver T g a m)

/-! ### The comparison is an isomorphism at an affine object -/

/-- The full open is contained in the preimage of the full open. -/
public theorem top_le_preimage_top {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (⊤ : X.Opens) ≤ f ⁻¹ᵁ ⊤ := by simp

/-- **`AlgebraicGeometry.Scheme.Hom.appLE` at the two full opens is the map `Scheme.Γ`
induces.**  The restriction map that `AlgebraicGeometry.Scheme.Hom.appLE` composes `f.app ⊤`
with is the identity, because `f ⁻¹ᵁ ⊤` *is* `⊤`.

This is the coherence the comparison needs: `Stacks.Sites.affineAssociatedBaseChangeIso`
extends scalars along `f.appLE ⊤ ⊤`, whereas the coordinate algebra `Stacks.Sites.gammaAlg` is
an algebra over its base through `Scheme.Γ.map`. -/
public theorem gammaMap_eq_appLE_top_top {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Γ.map f.op).hom = (f.appLE ⊤ ⊤ (top_le_preimage_top f)).hom :=
  congrArg CommRingCat.Hom.hom
    (((Scheme.Hom.appLE_eq_app f).trans (Scheme.Γ_map_op f).symm).symm)

/-- **`A ⊗[ULift R] M ≃+ A ⊗[R] M`.**  Tensoring over a universe lift of the base ring is
tensoring over the base ring, when the lifted ring acts through `ULift.down` on both factors.

The two module structures over `R` are taken as explicit arguments, and the ones over
`ULift R` are *forced* to be the ones they induce: with both an `R`- and a `ULift R`-structure
in scope as instances, `SMul (ULift R) A` has two resolutions — `ULift.smulLeft` and the
`ULift R`-module — and the statement would silently be about the wrong one.

This is the one step of the comparison that is not already available: the Amitsur side of
[Stacks, Tag 023L] tensors over `ULift R`, since `AlgebraicTopology.algebraMapArrow` lifts the
base ring to a common universe with the algebra, while the affine base-change comparison
tensors over `R` itself. -/
public def uliftBaseTensorAddEquiv (Rr : Type u) [CommRing Rr] (Aa : Type u) [AddCommGroup Aa]
    (Mm : Type*) [AddCommGroup Mm] (iA : Module Rr Aa) (iM : Module Rr Mm) :
    letI := iA
    letI := iM
    (@TensorProduct (ULift.{u} Rr) _ Aa Mm _ _ ULift.module ULift.module) ≃+
      (Aa ⊗[Rr] Mm) := by
  letI := iA
  letI := iM
  letI : Module (ULift.{u} Rr) Aa := ULift.module
  letI : Module (ULift.{u} Rr) Mm := ULift.module
  haveI : SMulCommClass Rr (ULift.{u} Rr) Aa := ⟨fun r c a => smul_comm r c.down a⟩
  haveI : SMulCommClass (ULift.{u} Rr) Rr Aa := ⟨fun c r a => smul_comm c.down r a⟩
  haveI : TensorProduct.CompatibleSMul Rr (ULift.{u} Rr) Aa Mm :=
    ⟨fun c a m => TensorProduct.smul_tmul c.down a m⟩
  haveI : TensorProduct.CompatibleSMul (ULift.{u} Rr) Rr Aa Mm :=
    ⟨fun r a m => TensorProduct.smul_tmul (ULift.up.{u} r) a m⟩
  exact (TensorProduct.equivOfCompatibleSMul Rr (ULift.{u} Rr) Rr Aa Mm).toAddEquiv

/-- The restriction maps of `Fᵃ` are the pullback maps on sections of [Stacks, Tag 03DS]. -/
public theorem associatedPresheaf_map_eq {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (associatedPresheaf S F toOver).map f = pullbackSectionsMap F (toOver.map f.unop) := rfl

section AffineBaseChange

variable {B W : Scheme.{u}} [IsAffine B] [IsAffine W] (N : B.Modules) [N.IsQuasicoherent]
  (q : W ⟶ B)

/-- **The affine base-change comparison of [Stacks, Tag 02KH] in degree zero, with the extended
ring map named.**  `AlgebraicGeometry.affinePullbackSectionsBaseChangeIso` at the two full
opens, stated for any ring map *equal* to `q.appLE ⊤ ⊤`, so that it can be composed with the
coordinate algebra of `Stacks.Sites.gammaAlg`, whose base acts through `Scheme.Γ.map`: the two
ring maps agree by `Stacks.Sites.gammaMap_eq_appLE_top_top`, but only propositionally, so the
module structure `CategoryTheory.ModuleCat.extendScalars` builds from one is not the one the
algebra provides. -/
public def affineBaseChangeIsoOfEq (φ : Γ(B, ⊤) →+* Γ(W, ⊤))
    (hφ : φ = (q.appLE ⊤ ⊤ (top_le_preimage_top q)).hom) :
    (ModuleCat.extendScalars φ).obj (ModuleCat.of Γ(B, ⊤) Γ(N, ⊤)) ≅
      ModuleCat.of Γ(W, ⊤) Γ((Scheme.Modules.pullback q).obj N, ⊤) := by
  subst hφ
  exact affinePullbackSectionsBaseChangeIso q N (isAffineOpen_top B) (isAffineOpen_top W)
    (top_le_preimage_top q)

/-- `Stacks.Sites.affineBaseChangeIsoOfEq` on the generators `1 ⊗ m`. -/
public theorem affineBaseChangeIsoOfEq_one_tmul (φ : Γ(B, ⊤) →+* Γ(W, ⊤))
    (hφ : φ = (q.appLE ⊤ ⊤ (top_le_preimage_top q)).hom) (m : Γ(N, ⊤)) :
    (affineBaseChangeIsoOfEq N q φ hφ).hom ((1 : Γ(W, ⊤)) ⊗ₜ[Γ(B, ⊤), φ] m) =
      Scheme.Modules.pullbackSection q N ⊤ ⊤ (top_le_preimage_top q) m := by
  subst hφ
  exact affinePullbackSectionsBaseChangeIso_one_tmul q N (isAffineOpen_top B)
    (isAffineOpen_top W) (top_le_preimage_top q) m

/-- `Stacks.Sites.affineBaseChangeIsoOfEq` on a general generator `a ⊗ m`: the comparison is
`Γ(W, 𝒪)`-linear, so the formula on `1 ⊗ m` determines it. -/
public theorem affineBaseChangeIsoOfEq_tmul (φ : Γ(B, ⊤) →+* Γ(W, ⊤))
    (hφ : φ = (q.appLE ⊤ ⊤ (top_le_preimage_top q)).hom) (a : Γ(W, ⊤)) (m : Γ(N, ⊤)) :
    (affineBaseChangeIsoOfEq N q φ hφ).hom (a ⊗ₜ[Γ(B, ⊤), φ] m) =
      a • (affineBaseChangeIsoOfEq N q φ hφ).hom ((1 : Γ(W, ⊤)) ⊗ₜ[Γ(B, ⊤), φ] m) := by
  let _ : Algebra (Γ(B, ⊤) : Type u) (Γ(W, ⊤) : Type u) := φ.toAlgebra
  have h1 : (a ⊗ₜ[Γ(B, ⊤), φ] m) = a • ((1 : Γ(W, ⊤)) ⊗ₜ[Γ(B, ⊤), φ] m) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  exact (congrArg (fun y => (affineBaseChangeIsoOfEq N q φ hφ).hom y) h1).trans
    ((affineBaseChangeIsoOfEq N q φ hφ).hom.hom.map_smul a
      ((1 : Γ(W, ⊤)) ⊗ₜ[Γ(B, ⊤), φ] m))

end AffineBaseChange

/-- The coordinate-ring map of the structure morphism of an object of `Over T`: the ring map
the affine base-change comparison extends scalars along, and — by
`Stacks.Sites.gammaAlg_algebraMap` — the one the lifted base ring acts on the coordinate
algebra through. -/
public abbrev coeffRingMap (Z : (Over T)ᵒᵖ) :
    Γ((toOver.obj T).left, ⊤) →+* Γ((toOver.obj Z.unop.left).left, ⊤) :=
  (Scheme.Γ.map (toOver.map Z.unop.hom).left.op).hom

/-- `Stacks.Sites.gammaMap_eq_appLE_top_top` at `Stacks.Sites.coeffRingMap`, in the spelling
the affine base-change comparison asks for. -/
public theorem coeffRingMap_eq (Z : (Over T)ᵒᵖ) :
    coeffRingMap S toOver T Z =
      ((toOver.map Z.unop.hom).left.appLE ⊤ ⊤
        (top_le_preimage_top (toOver.map Z.unop.hom).left)).hom :=
  gammaMap_eq_appLE_top_top _

variable [IsAffine (toOver.obj T).left]

/-- **The coefficient comparison is an isomorphism at an object of `Over T` with affine total
space.**  Both sides are additive maps out of `Γ(Z, 𝒪) ⊗ Fᵃ(T)` and agree on the generators
`a ⊗ m`, where `Stacks.Sites.affineBaseChangeIsoOfEq_one_tmul` and
`Stacks.Sites.pullbackSectionsComparison_pullbackSection` identify the affine base-change
comparison of [Stacks, Tag 02KH] with the restriction map of `Fᵃ`.

This is the clause that genuinely needs affineness, and it is why the full-slice form of the
coefficient hypothesis of [Stacks, Tag 03FJ] is unavailable: at a non-affine `Z` over an
affine `T` the comparison is not an isomorphism. -/
public theorem isIso_tensorToSectionsApp (Z : (Over T)ᵒᵖ)
    [IsAffine (toOver.obj Z.unop.left).left] :
    IsIso (tensorToSectionsApp S F toOver T Z) := by
  classical
  let iA : Module (Γ((toOver.obj T).left, ⊤) : Type u)
      (Γ((toOver.obj Z.unop.left).left, ⊤) : Type u) :=
    Module.compHom _ (coeffRingMap S toOver T Z)
  let e := sectionsLinearEquivOfIso (pullbackSectionsComparison F (toOver.map Z.unop.hom)) ⊤
  let I := affineBaseChangeIsoOfEq ((Scheme.Modules.pullback (toOver.obj T).hom).obj F)
    (toOver.map Z.unop.hom).left (coeffRingMap S toOver T Z) (coeffRingMap_eq S toOver T Z)
  let E := uliftBaseTensorAddEquiv (Γ((toOver.obj T).left, ⊤))
    (Γ((toOver.obj Z.unop.left).left, ⊤)) (coeffModule S F toOver T) iA
    (instModuleCoeffSections S F toOver T)
  obtain ⟨Ψ, hbij, hΨ⟩ : ∃ Ψ : _ →+ _, Function.Bijective Ψ ∧
      tensorToSectionsApp S F toOver T Z = AddCommGrpCat.ofHom Ψ := by
    refine ⟨e.toLinearMap.toAddMonoidHom.comp
        (I.hom.hom.toAddMonoidHom.comp E.toAddMonoidHom), ?_, ?_⟩
    · exact e.bijective.comp
        ((ConcreteCategory.bijective_of_isIso I.hom).comp E.bijective)
    · apply AddCommGrpCat.hom_ext
      let _ : Module (ULift.{u} (coeffBase S toOver T))
          (Γ((toOver.obj Z.unop.left).left, ⊤) : Type u) :=
        inferInstanceAs (Module (ULift.{u} (coeffBase S toOver T))
          (((gammaAlg S toOver T).obj Z : CommAlgCat.{u} _) : Type u))
      refine addHom_ext_tmul (Rr := ULift.{u} (coeffBase S toOver T))
        (Mm := (Γ((toOver.obj Z.unop.left).left, ⊤) : Type u))
        (Nn := coeffModule S F toOver T)
        (Pp := (((Over.forget T).op ⋙ associatedPresheaf S F toOver).obj Z : Type u))
        (fun a m => ?_)
      have h2 := affineBaseChangeIsoOfEq_tmul _ _ _ (coeffRingMap_eq S toOver T Z) a m
      have h3 := affineBaseChangeIsoOfEq_one_tmul _ _ _ (coeffRingMap_eq S toOver T Z) m
      have h4 := pullbackSectionsComparison_pullbackSection F (toOver.map Z.unop.hom)
        (top_le_preimage_top (toOver.map Z.unop.hom).left) m
      have hstep := (congrArg (fun y => e y) h2).trans
        ((map_smul e a _).trans (congrArg (fun y => a • y) ((congrArg (fun y => e y) h3).trans h4)))
      exact (tensorToSectionsApp_tmul S F toOver T Z a m).trans hstep.symm
  rw [hΨ]
  exact (ConcreteCategory.isIso_iff_bijective _).2 hbij

end Stacks.Sites

end
