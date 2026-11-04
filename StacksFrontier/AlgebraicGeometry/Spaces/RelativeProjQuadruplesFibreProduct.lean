module

public import StacksFrontier.AlgebraicGeometry.Spaces.FibreDegreeStratification
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjQuadruplesLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjQuadruplesSections

/-!
# The base change of the functor of quadruples to a scheme is the relative Proj

In Situation 0849 let `X` be an algebraic space over a scheme `S`, `𝒜` a quasi-coherent graded
`𝒪_X`-algebra and `F` the functor of quadruples of Stacks 084A.  The second assertion of Stacks
084B is a canonical isomorphism `Proj_Z(g^*𝒜) = Z ×_X F` for every morphism `g : Z ⟶ X` from a
scheme.  The source's proof: the functor `F'` of quadruples of `g^*𝒜` on `Z` is `Z ×_X F`, by
sending a quadruple `(d, f : T → Z, ℒ, ψ)` to `(d, g ∘ f, ℒ, ψ)`, and `F'` is represented by
`Proj_Z(g^*𝒜)` by Tags 01NY and 01NZ.

This file carries out that proof on the points of the two presheaves.  For a test object `T`, a
`T`-point of `Z ×_X F` is a morphism `t : T ⟶ Z` together with a point of `F(T)` over `g ∘ t`, and
`AlgebraicGeometry.Space.GradedAlgebraRestriction.projEquiv` identifies these with the morphisms
`T ⟶ Proj_Z(g^*𝒜)` over `S`, naturally in `T`
(`AlgebraicGeometry.Space.GradedAlgebraRestriction.projEquiv_comp`).

## Main definitions

* `AlgebraicGeometry.Space.GradedAlgebraRestriction.fibreOfF`: the inverse of the comparison
  `AlgebraicGeometry.Space.GradedAlgebraRestriction.fibreToF` on the points lying over `t`; it is
  the source's "sending `(d, f, ℒ, ψ)` to `(d, g ∘ f, ℒ, ψ)`".
* `AlgebraicGeometry.Space.GradedAlgebraRestriction.projObj`: `Proj_Z(g^*𝒜)` as an object of the
  big fppf site over `S`, and `AlgebraicGeometry.Space.GradedAlgebraRestriction.projHom` its
  structure morphism to `Z`.
* `AlgebraicGeometry.Space.GradedAlgebraRestriction.projEquiv`: the bijection between the
  `T`-points of `Proj_Z(g^*𝒜)` and the `T`-points of `Z ×_X F`.

## Implementation notes

The restriction `f^*𝒜` of the graded algebra to the scheme points `f` of `X` is taken as a family
`Â` of graded algebra data of Situation 01NN on the schemes of the test objects, which is what
the representability of Tags 01NY and 01NZ needs, and the restriction datum is over the datum of
Stacks 084A it induces (`AlgebraicGeometry.Space.GradedAlgebraPoints.ofQuasicoherentFamily`).
That `Proj_Z(g^*𝒜)` is an object of the site — a statement about the size of `g^*𝒜` — is a
hypothesis of `projObj`; in Situation 0849 it is
`AlgebraicGeometry.Space.RelativeProjSituation.contains_relativeProj_pointAlgebra`.

The source's `F(T)` for a non-quasi-compact `T` is a limit over the quasi-compact opens of `T`,
and so is the functor `F'` of Tag 01NY; the two limits are compared through the quasi-compact
opens of the scheme of `T`, which are objects of the site (`AlgebraicGeometry.Space.opensObject`),
using `AlgebraicGeometry.Scheme.QcExtension.equivQcOpen`.

## References

* [Stacks Project, Tag 084B](https://stacks.math.columbia.edu/tag/084B)
* [Stacks Project, Tag 01NT](https://stacks.math.columbia.edu/tag/01NT)
* [Stacks Project, Tag 01NY](https://stacks.math.columbia.edu/tag/01NY)
* [Stacks Project, Tag 01NZ](https://stacks.math.columbia.edu/tag/01NZ)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

open AlgebraicGeometry Stacks.RingedSpace
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

universe u

namespace AlgebraicGeometry.Space

namespace GradedAlgebraRestriction

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### The inverse of the comparison -/

section Inverse

variable {r : GradedAlgebraPoints B S hS X} (ρ : GradedAlgebraRestriction r)

/-- **A point of the scheme-level functor of quadruples of `g^*𝒜` over `t`, as a point of the
fibre of `F(T)` over the restricted point `t^*g`.** The class over `t` is base changed down along
`t` to a class over the identity of `T` for `t^*(g^*𝒜)` by Tag 01NT, and transported along the
comparison `(g ∘ t)^*𝒜 ≅ t^*(g^*𝒜)` of the restriction datum. -/
def fibreOfF {Z T : BigFppfOver B S hS} (g : yoneda.obj Z ⟶ X) (t : T ⟶ Z)
    (f : yoneda.obj T ⟶ X) (hf : yoneda.map t ≫ g = f)
    (ζ : F (r.algebra Z g) ((BigFppfOver.toScheme B S hS).obj T))
    (hζ : ζ.1 = (BigFppfOver.toScheme B S hS).map t) : GradedAlgebraPoints.F.fibre r T f :=
  (F.algebraTransport (ρ.restrict t g f hf) (ρ.isIso_restrict_app t g f hf)
    (F.baseChangeDownQ ((BigFppfOver.toScheme B S hS).map t) (r.algebra Z g) (𝟙 _)
      (cast (congrArg (fun k => Quot (UnionRel (f := k) (A := r.algebra Z g))) hζ) ζ.2))).2

/-- `fibreOfF` is a right inverse of the comparison. -/
theorem fibreToF_fibreOfF {Z T : BigFppfOver B S hS} (g : yoneda.obj Z ⟶ X) (t : T ⟶ Z)
    (f : yoneda.obj T ⟶ X) (hf : yoneda.map t ≫ g = f)
    (ζ : F (r.algebra Z g) ((BigFppfOver.toScheme B S hS).obj T))
    (hζ : ζ.1 = (BigFppfOver.toScheme B S hS).map t) :
    ρ.fibreToF g t f hf (ρ.fibreOfF g t f hf ζ hζ) = ζ := by
  obtain ⟨k, c⟩ := ζ
  obtain rfl : k = (BigFppfOver.toScheme B S hS).map t := hζ
  show F.baseChangeUp _ _ ((F.algebraTransportEquiv _ _ _).symm
    (F.algebraTransportEquiv _ _ _ (F.baseChangeDownQ _ _ (𝟙 _) c))) = _
  rw [Equiv.symm_apply_apply]
  exact F.baseChangeUp_baseChangeDownQ _ _ (𝟙 _) c

/-- `fibreOfF` is a left inverse of the comparison. -/
theorem fibreOfF_fibreToF {Z T : BigFppfOver B S hS} (g : yoneda.obj Z ⟶ X) (t : T ⟶ Z)
    (f : yoneda.obj T ⟶ X) (hf : yoneda.map t ≫ g = f) (q : GradedAlgebraPoints.F.fibre r T f) :
    ρ.fibreOfF g t f hf (ρ.fibreToF g t f hf q) rfl = q :=
  ρ.fibreToF_injective g t f hf (ρ.fibreToF_fibreOfF g t f hf _ rfl)

/-- `fibreOfF` respects equalities in all its arguments. -/
theorem fibreOfF_heq {Z T : BigFppfOver B S hS} (g : yoneda.obj Z ⟶ X) {t t' : T ⟶ Z}
    {f f' : yoneda.obj T ⟶ X} (hf : yoneda.map t ≫ g = f) (hf' : yoneda.map t' ≫ g = f')
    {ζ ζ' : F (r.algebra Z g) ((BigFppfOver.toScheme B S hS).obj T)}
    (hζ : ζ.1 = (BigFppfOver.toScheme B S hS).map t)
    (hζ' : ζ'.1 = (BigFppfOver.toScheme B S hS).map t') (ht : t = t') (hff : f = f')
    (hζζ : ζ = ζ') : HEq (ρ.fibreOfF g t f hf ζ hζ) (ρ.fibreOfF g t' f' hf' ζ' hζ') := by
  subst ht hff hζζ
  rfl

/-- The comparison applied to the point a family records at a morphism depends on the morphism
only through its value. -/
theorem fibreToF_val_congr {Z T W : BigFppfOver B S hS} (g : yoneda.obj Z ⟶ X) (t : T ⟶ Z)
    (ξ : LimPoint ρ T) (hW : CompactSpace ((BigFppfOver.toScheme B S hS).obj W))
    {w w' : W ⟶ T} (hww : w = w') (hf : yoneda.map (w ≫ t) ≫ g = yoneda.map w ≫ ξ.point)
    (hf' : yoneda.map (w' ≫ t) ≫ g = yoneda.map w' ≫ ξ.point) :
    ρ.fibreToF g (w ≫ t) _ hf (ξ.val W hW w) = ρ.fibreToF g (w' ≫ t) _ hf' (ξ.val W hW w') := by
  subst hww
  rfl

end Inverse

/-! ### The base condition of the representation of Tags 01NY and 01NZ -/

/-- **The point of the functor of Tag 01NY attached to a morphism into the relative Proj lies over
the composite with the structure morphism**, at every quasi-compact test scheme. -/
theorem homEquiv_val_fst {Y : Scheme.{u}} (A : SheafGradedAlgebra Y) {T : Scheme.{u}}
    (k : T ⟶ (relativeProj A).scheme) (W : Scheme.{u}) (hW : CompactSpace W) (w : W ⟶ T) :
    (((relativeProjRepresentableByFunctorUnconditional A).homEquiv k).val W hW w).1 =
      w ≫ k ≫ (relativeProj A).toBase := by
  set R := relativeProjRepresentableByFunctorUnconditional A
  have h1 : (R.homEquiv k).val W hW w = (R.homEquiv (w ≫ k)).val W hW (𝟙 W) := by
    rw [R.homEquiv_comp]
    rfl
  have h2 : Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.F.toLim A
      ((R.homEquiv (w ≫ k)).val W hW (𝟙 W)) = R.homEquiv (w ≫ k) :=
    (GradedAlgebraPoints.F.limEquiv_symm_eq_toLim A W hW _).symm.trans
      ((F.limEquiv (situationAlgebra A) W hW).symm_apply_apply (R.homEquiv (w ≫ k)))
  calc ((R.homEquiv k).val W hW w).1 = ((R.homEquiv (w ≫ k)).val W hW (𝟙 W)).1 :=
        congrArg Sigma.fst h1
    _ = R.homEquiv.symm (R.homEquiv (w ≫ k)) ≫ (relativeProj A).toBase :=
        (Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.homEquiv_symm_toLim_comp_toBase
          A ((R.homEquiv (w ≫ k)).val W hW (𝟙 W))).symm.trans
          (congrArg (fun z => R.homEquiv.symm z ≫ (relativeProj A).toBase) h2)
    _ = w ≫ k ≫ (relativeProj A).toBase := by
        rw [Equiv.symm_apply_apply, Category.assoc]

/-! ### The relative Proj of a scheme point as an object of the site -/

variable (Â : ∀ T : BigFppfOver B S hS, (yoneda.obj T ⟶ X) →
  SheafGradedAlgebra ((BigFppfOver.toScheme B S hS).obj T))

/-- **`Proj_Z(g^*𝒜)` as an object of the big fppf site over `S`**, for a scheme point
`g : Z ⟶ X` whose relative Proj is contained in the site. -/
def projObj {Z : BigFppfOver B S hS} (g : yoneda.obj Z ⟶ X)
    (hc : B.Contains (relativeProj (Â Z g)).scheme) : BigFppfOver B S hS :=
  BigFppfOver.mk B S hS hc ((relativeProj (Â Z g)).toBase ≫ B.inclusion.map Z.hom)

/-- The scheme underlying `projObj Â g hc` is `Proj_Z(g^*𝒜)`. -/
@[simp] theorem toScheme_obj_projObj {Z : BigFppfOver B S hS} (g : yoneda.obj Z ⟶ X)
    (hc : B.Contains (relativeProj (Â Z g)).scheme) :
    (BigFppfOver.toScheme B S hS).obj (projObj Â g hc) = (relativeProj (Â Z g)).scheme := rfl

/-- The structure morphism `Proj_Z(g^*𝒜) ⟶ Z`, as a morphism of the site. -/
def projHom {Z : BigFppfOver B S hS} (g : yoneda.obj Z ⟶ X)
    (hc : B.Contains (relativeProj (Â Z g)).scheme) : projObj Â g hc ⟶ Z :=
  Over.homMk (ObjectProperty.homMk (relativeProj (Â Z g)).toBase)
    (by apply ObjectProperty.hom_ext; rfl)

/-- The morphism of schemes underlying `projHom Â g hc` is the structure morphism of
`Proj_Z(g^*𝒜)`. -/
@[simp] theorem toScheme_map_projHom {Z : BigFppfOver B S hS} (g : yoneda.obj Z ⟶ X)
    (hc : B.Contains (relativeProj (Â Z g)).scheme) :
    (BigFppfOver.toScheme B S hS).map (projHom Â g hc) = (relativeProj (Â Z g)).toBase := rfl

/-! ### The two directions -/

variable {Â} (ρ : GradedAlgebraRestriction (GradedAlgebraPoints.ofQuasicoherentFamily Â))

/-- **From the functor `F'` of quadruples of `g^*𝒜` to `Z ×_X F`.** A point `ζ` of the extension
of `F'` over the quasi-compact test schemes of `T`, lying over `t`, gives the point of `F(T)` over
`g ∘ t` whose value at `w : W ⟶ T` is the point of the fibre corresponding to the value of `ζ` at
`w`. -/
def limPointOfQc {Z T : BigFppfOver B S hS} (g : yoneda.obj Z ⟶ X) (t : T ⟶ Z)
    (ζ : Scheme.QcExtension (F.functor (situationAlgebra (Â Z g)))
      ((BigFppfOver.toScheme B S hS).obj T))
    (hζ : ∀ (W : Scheme.{u}) (hW : CompactSpace W)
      (w : W ⟶ (BigFppfOver.toScheme B S hS).obj T),
      (ζ.val W hW w).1 = w ≫ (BigFppfOver.toScheme B S hS).map t) : LimPoint ρ T where
  point := yoneda.map t ≫ g
  val _ hW w := ρ.fibreOfF g (w ≫ t) _ rfl (ζ.val _ hW ((BigFppfOver.toScheme B S hS).map w))
    (hζ _ hW _)
  compat _ _ hW hW' h w :=
    ρ.fibreToF_injective g ((h ≫ w) ≫ t) (yoneda.map (h ≫ w) ≫ yoneda.map t ≫ g) rfl <|
      (ρ.fibreToF_fibreRestrict g (w ≫ t) h (yoneda.map w ≫ yoneda.map t ≫ g)
        (yoneda.map (h ≫ w) ≫ yoneda.map t ≫ g) rfl rfl rfl _).trans
        ((congrArg (F.pullback ((BigFppfOver.toScheme B S hS).map h))
          (ρ.fibreToF_fibreOfF g (w ≫ t) _ rfl _ (hζ _ hW _))).trans
          ((ζ.compat _ _ hW hW' _ _).trans (ρ.fibreToF_fibreOfF g ((h ≫ w) ≫ t) _ rfl _
            (hζ _ hW' _)).symm))

/-- The site morphism `V ⟶ V'` of two opens of the scheme of `T` with `V ≤ V'`. -/
def opensObjectHomOfLE (T : BigFppfOver B S hS)
    {V V' : ((BigFppfOver.toScheme B S hS).obj T).Opens} (h : V ≤ V') :
    opensObject B S hS T V ⟶ opensObject B S hS T V' :=
  Over.homMk (ObjectProperty.homMk (((BigFppfOver.toScheme B S hS).obj T).homOfLE h))
    (by
      apply ObjectProperty.hom_ext
      exact (Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ B.inclusion.map T.hom) (Scheme.homOfLE_ι _ h)))

/-- The morphism `opensObjectHomOfLE T h` composed with the inclusion of `V'` is the inclusion of
`V`. -/
theorem opensObjectHomOfLE_ι (T : BigFppfOver B S hS)
    {V V' : ((BigFppfOver.toScheme B S hS).obj T).Opens} (h : V ≤ V') :
    opensObjectHomOfLE T h ≫ opensObjectι B S hS T V' = opensObjectι B S hS T V :=
  BigFppfOver.map_toScheme_injective B S hS (Scheme.homOfLE_ι _ h)

/-- **From `Z ×_X F` to the functor `F'` of quadruples of `g^*𝒜`, on the quasi-compact opens.**
A point of `F(T)` over `g ∘ t` gives, at every quasi-compact open `V` of the scheme of `T`, the
point of `F'(V)` over `t|_V` corresponding to its value at `V`. -/
def qcOpenOfLimPoint {Z T : BigFppfOver B S hS} (g : yoneda.obj Z ⟶ X) (t : T ⟶ Z)
    (ξ : LimPoint ρ T) (hξ : ξ.point = yoneda.map t ≫ g) :
    Scheme.QcOpenExtension (F.functor (situationAlgebra (Â Z g)))
      ((BigFppfOver.toScheme B S hS).obj T) where
  val V hV := ρ.fibreToF g (opensObjectι B S hS T V ≫ t) _ (by rw [hξ]; rfl)
    (ξ.val (opensObject B S hS T V) (isCompact_iff_compactSpace.mp hV)
      (opensObjectι B S hS T V))
  compat V V' hV hV' h :=
    (ρ.fibreToF_fibreRestrict g (opensObjectι B S hS T V ≫ t) (opensObjectHomOfLE T h)
      (yoneda.map (opensObjectι B S hS T V) ≫ ξ.point)
      (yoneda.map (opensObjectHomOfLE T h ≫ opensObjectι B S hS T V) ≫ ξ.point)
      (by rw [hξ]; rfl) rfl (by rw [hξ]; rfl) _).symm.trans
      ((congrArg (ρ.fibreToF g (opensObjectHomOfLE T h ≫ opensObjectι B S hS T V ≫ t)
        (yoneda.map (opensObjectHomOfLE T h ≫ opensObjectι B S hS T V) ≫ ξ.point)
        (by rw [hξ]; rfl)) (ξ.compat _ _ _ _ _ _)).trans
        (ρ.fibreToF_val_congr g t ξ _ (opensObjectHomOfLE_ι T h) _ _))

/-- The extension of `F'` attached to a point of `Z ×_X F`. -/
def qcOfLimPoint {Z T : BigFppfOver B S hS} (g : yoneda.obj Z ⟶ X) (t : T ⟶ Z)
    (ξ : LimPoint ρ T) (hξ : ξ.point = yoneda.map t ≫ g) :
    Scheme.QcExtension (F.functor (situationAlgebra (Â Z g)))
      ((BigFppfOver.toScheme B S hS).obj T) :=
  (Scheme.QcExtension.equivQcOpen _ _).symm (ρ.qcOpenOfLimPoint g t ξ hξ)

/-- A morphism out of a test object with quasi-compact scheme, factored through a quasi-compact
open of the scheme of the target, as a morphism of the site. -/
def factorHom {T W : BigFppfOver B S hS} (w : W ⟶ T)
    (c : Scheme.CompactOpenFactorization ((BigFppfOver.toScheme B S hS).map w)) :
    W ⟶ opensObject B S hS T c.opens :=
  Over.homMk (ObjectProperty.homMk c.hom) (by
    apply ObjectProperty.hom_ext
    change c.hom ≫ c.opens.ι ≫ B.inclusion.map T.hom = B.inclusion.map W.hom
    rw [← Category.assoc, c.fac]
    exact congrArg B.inclusion.map (Over.w w))

/-- The factorization `factorHom w c` composed with the inclusion of the open `c.opens` is `w`. -/
theorem factorHom_ι {T W : BigFppfOver B S hS} (w : W ⟶ T)
    (c : Scheme.CompactOpenFactorization ((BigFppfOver.toScheme B S hS).map w)) :
    factorHom w c ≫ opensObjectι B S hS T c.opens = w :=
  BigFppfOver.map_toScheme_injective B S hS c.fac

/-- **The extension attached to a point of `Z ×_X F`, at a quasi-compact test object**: its value
at `w : W ⟶ T` is the point of `F'(W)` corresponding to the value of the point of `F(T)` at
`w`. -/
theorem qcOfLimPoint_val {Z T : BigFppfOver B S hS} (g : yoneda.obj Z ⟶ X) (t : T ⟶ Z)
    (ξ : LimPoint ρ T) (hξ : ξ.point = yoneda.map t ≫ g) (W : BigFppfOver B S hS)
    (hW : CompactSpace ((BigFppfOver.toScheme B S hS).obj W)) (w : W ⟶ T) :
    (ρ.qcOfLimPoint g t ξ hξ).val _ hW ((BigFppfOver.toScheme B S hS).map w) =
      ρ.fibreToF g (w ≫ t) _ (by rw [hξ]; rfl) (ξ.val W hW w) := by
  set c := Scheme.compactOpenFactorization hW ((BigFppfOver.toScheme B S hS).map w)
  show F.pullback c.hom (ρ.qcOpenOfLimPoint g t ξ hξ |>.val c.opens c.isCompact_opens) = _
  exact (ρ.fibreToF_fibreRestrict g (opensObjectι B S hS T c.opens ≫ t) (factorHom w c)
      (yoneda.map (opensObjectι B S hS T c.opens) ≫ ξ.point)
      (yoneda.map (factorHom w c ≫ opensObjectι B S hS T c.opens) ≫ ξ.point)
      (by rw [hξ]; rfl) rfl (by rw [hξ]; rfl) _).symm.trans
      ((congrArg (ρ.fibreToF g (factorHom w c ≫ opensObjectι B S hS T c.opens ≫ t)
        (yoneda.map (factorHom w c ≫ opensObjectι B S hS T c.opens) ≫ ξ.point)
        (by rw [hξ]; rfl)) (ξ.compat _ _ _ _ _ _)).trans
        (ρ.fibreToF_val_congr g t ξ _ (factorHom_ι w c) _ _))

/-- The extension attached to a point of `Z ×_X F` over `t` lies over `t`. -/
theorem qcOfLimPoint_val_fst {Z T : BigFppfOver B S hS} (g : yoneda.obj Z ⟶ X) (t : T ⟶ Z)
    (ξ : LimPoint ρ T) (hξ : ξ.point = yoneda.map t ≫ g) (W : Scheme.{u}) (hW : CompactSpace W)
    (w : W ⟶ (BigFppfOver.toScheme B S hS).obj T) :
    ((ρ.qcOfLimPoint g t ξ hξ).val W hW w).1 = w ≫ (BigFppfOver.toScheme B S hS).map t := by
  set c := Scheme.compactOpenFactorization hW w
  show c.hom ≫ c.opens.ι ≫ (BigFppfOver.toScheme B S hS).map t = _
  rw [← Category.assoc, c.fac]

/-! ### The bijection -/

/-- The point recorded by `q` at `w` is unchanged by passing through the representing bijection
and back. -/
private theorem homEquiv_homEquiv_symm_val {Y : Scheme.{u}} (A : SheafGradedAlgebra Y)
    {T : Scheme.{u}} (q : Scheme.QcExtension (F.functor (situationAlgebra A)) T) (W : Scheme.{u})
    (hW : CompactSpace W) (w : W ⟶ T) :
    ((relativeProjRepresentableByFunctorUnconditional A).homEquiv
      ((relativeProjRepresentableByFunctorUnconditional A).homEquiv.symm q)).val W hW w =
        q.val W hW w :=
  congrArg (fun z : Scheme.QcExtension _ T => z.val W hW w) (Equiv.apply_symm_apply _ _)

/-- **The morphism into the relative Proj attached to a point of `Z ×_X F` lies over `t`.**  Its
composite with the structure morphism agrees with `t` on every quasi-compact open of the scheme of
`T`, by the base condition of the representation, and the quasi-compact opens cover. -/
theorem homEquiv_symm_qcOfLimPoint_comp_toBase {Z T : BigFppfOver B S hS}
    (g : yoneda.obj Z ⟶ X) (t : T ⟶ Z) (ξ : LimPoint ρ T) (hξ : ξ.point = yoneda.map t ≫ g) :
    (relativeProjRepresentableByFunctorUnconditional (Â Z g)).homEquiv.symm
        (ρ.qcOfLimPoint g t ξ hξ) ≫ (relativeProj (Â Z g)).toBase =
      (BigFppfOver.toScheme B S hS).map t := by
  set R := relativeProjRepresentableByFunctorUnconditional (Â Z g)
  obtain ⟨φ, -, huniq⟩ := Scheme.existsUnique_hom_of_compatible_compactOpens
    ((BigFppfOver.toScheme B S hS).obj T)
    (fun V _ => V.ι ≫ (BigFppfOver.toScheme B S hS).map t)
    (fun V W _ _ h => by rw [← Category.assoc, Scheme.homOfLE_ι])
  refine (huniq _ fun V hV => ?_).trans (huniq _ fun V hV => rfl).symm
  have h1 := homEquiv_val_fst (Â Z g) (R.homEquiv.symm (ρ.qcOfLimPoint g t ξ hξ)) V.toScheme
    (isCompact_iff_compactSpace.mp hV) V.ι
  have h2 := ρ.qcOfLimPoint_val_fst g t ξ hξ V.toScheme (isCompact_iff_compactSpace.mp hV) V.ι
  exact h1.symm.trans ((congrArg Sigma.fst (homEquiv_homEquiv_symm_val (Â Z g) _ _
    (isCompact_iff_compactSpace.mp hV) _)).trans h2)

/-- **The point of `Z ×_X F` attached to a `T`-point of `Proj_Z(g^*𝒜)`**: the point of `F(T)`
corresponding, through the source's `(d, f, ℒ, ψ) ↦ (d, g ∘ f, ℒ, ψ)`, to the point of the functor
of quadruples of `g^*𝒜` which the representation of Tags 01NY and 01NZ attaches to it. -/
def projPoint {Z T : BigFppfOver B S hS} (g : yoneda.obj Z ⟶ X)
    (hc : B.Contains (relativeProj (Â Z g)).scheme) (s : T ⟶ projObj Â g hc) : LimPoint ρ T :=
  ρ.limPointOfQc g (s ≫ projHom Â g hc)
    ((relativeProjRepresentableByFunctorUnconditional (Â Z g)).homEquiv
      ((BigFppfOver.toScheme B S hS).map s))
    (fun W hW w => homEquiv_val_fst _ _ W hW w)

/-- The point of `Z ×_X F` attached to `s : T ⟶ Proj_Z(g^*𝒜)` lies over the composite of `s`,
the structure morphism to `Z` and `g`. -/
@[simp] theorem projPoint_point {Z T : BigFppfOver B S hS} (g : yoneda.obj Z ⟶ X)
    (hc : B.Contains (relativeProj (Â Z g)).scheme) (s : T ⟶ projObj Â g hc) :
    (ρ.projPoint g hc s).point = yoneda.map (s ≫ projHom Â g hc) ≫ g := rfl

/-- **The `T`-point of `Proj_Z(g^*𝒜)` attached to a point of `Z ×_X F`**, through the
representation of Tags 01NY and 01NZ. -/
def projHomOf {Z T : BigFppfOver B S hS} (g : yoneda.obj Z ⟶ X)
    (hc : B.Contains (relativeProj (Â Z g)).scheme) (t : T ⟶ Z) (ξ : LimPoint ρ T)
    (hξ : ξ.point = yoneda.map t ≫ g) : T ⟶ projObj Â g hc :=
  BigFppfOver.homMk B S hS hc _
    ((relativeProjRepresentableByFunctorUnconditional (Â Z g)).homEquiv.symm
      (ρ.qcOfLimPoint g t ξ hξ))
    (by
      rw [← Category.assoc, ρ.homEquiv_symm_qcOfLimPoint_comp_toBase]
      exact (B.inclusion.map_comp _ _).symm.trans (congrArg B.inclusion.map (Over.w t)))

/-- The morphism of schemes underlying `projHomOf g hc t ξ hξ` is the morphism into the relative
Proj which the representation attaches to `qcOfLimPoint g t ξ hξ`. -/
theorem toScheme_map_projHomOf {Z T : BigFppfOver B S hS} (g : yoneda.obj Z ⟶ X)
    (hc : B.Contains (relativeProj (Â Z g)).scheme) (t : T ⟶ Z) (ξ : LimPoint ρ T)
    (hξ : ξ.point = yoneda.map t ≫ g) :
    (BigFppfOver.toScheme B S hS).map (ρ.projHomOf g hc t ξ hξ) =
      (relativeProjRepresentableByFunctorUnconditional (Â Z g)).homEquiv.symm
        (ρ.qcOfLimPoint g t ξ hξ) := rfl

/-- The `T`-point `projHomOf g hc t ξ hξ` of `Proj_Z(g^*𝒜)` lies over `t`. -/
theorem projHomOf_comp_projHom {Z T : BigFppfOver B S hS} (g : yoneda.obj Z ⟶ X)
    (hc : B.Contains (relativeProj (Â Z g)).scheme) (t : T ⟶ Z) (ξ : LimPoint ρ T)
    (hξ : ξ.point = yoneda.map t ≫ g) : ρ.projHomOf g hc t ξ hξ ≫ projHom Â g hc = t :=
  BigFppfOver.map_toScheme_injective B S hS (ρ.homEquiv_symm_qcOfLimPoint_comp_toBase g t ξ hξ)

/-- `projHomOf` is a left inverse of `projPoint`: the `T`-point of `Proj_Z(g^*𝒜)` attached to
`projPoint g hc s` is `s`. -/
theorem projHomOf_projPoint {Z T : BigFppfOver B S hS} (g : yoneda.obj Z ⟶ X)
    (hc : B.Contains (relativeProj (Â Z g)).scheme) (s : T ⟶ projObj Â g hc) :
    ρ.projHomOf g hc (s ≫ projHom Â g hc) (ρ.projPoint g hc s) rfl = s := by
  apply BigFppfOver.map_toScheme_injective B S hS
  refine (Equiv.symm_apply_eq _).mpr ?_
  refine ((Scheme.QcExtension.equivQcOpen _ _).symm_apply_eq).mpr ?_
  ext V hV
  exact ρ.fibreToF_fibreOfF g (opensObjectι B S hS T V ≫ s ≫ projHom Â g hc) _ rfl _
    (homEquiv_val_fst _ _ _ _ _)

/-- `projHomOf` is a right inverse of `projPoint`: the point of `Z ×_X F` attached to
`projHomOf g hc t ξ hξ` is `ξ`. -/
theorem projPoint_projHomOf {Z T : BigFppfOver B S hS} (g : yoneda.obj Z ⟶ X)
    (hc : B.Contains (relativeProj (Â Z g)).scheme) (t : T ⟶ Z) (ξ : LimPoint ρ T)
    (hξ : ξ.point = yoneda.map t ≫ g) : ρ.projPoint g hc (ρ.projHomOf g hc t ξ hξ) = ξ := by
  have ht := ρ.projHomOf_comp_projHom g hc t ξ hξ
  apply LimPoint.ext'
  · rw [projPoint_point, ht, hξ]
  · intro W hW w
    have hval : ((relativeProjRepresentableByFunctorUnconditional (Â Z g)).homEquiv
        ((BigFppfOver.toScheme B S hS).map (ρ.projHomOf g hc t ξ hξ))).val _ hW
          ((BigFppfOver.toScheme B S hS).map w) =
        ρ.fibreToF g (w ≫ t) (yoneda.map w ≫ ξ.point) (by rw [hξ]; rfl) (ξ.val W hW w) :=
      (homEquiv_homEquiv_symm_val (Â Z g) (ρ.qcOfLimPoint g t ξ hξ) _ hW _).trans
        (ρ.qcOfLimPoint_val g t ξ hξ W hW w)
    have hw1 : w ≫ ρ.projHomOf g hc t ξ hξ ≫ projHom Â g hc = w ≫ t := by rw [ht]
    have hw2 : yoneda.map w ≫ yoneda.map (ρ.projHomOf g hc t ξ hξ ≫ projHom Â g hc) ≫ g =
        yoneda.map w ≫ ξ.point := by rw [ht, hξ]
    exact (ρ.fibreOfF_heq g rfl (by rw [hξ]; rfl) (homEquiv_val_fst _ _ _ _ _)
      rfl hw1 hw2 hval).trans
      (heq_of_eq (ρ.fibreOfF_fibreToF g (w ≫ t) _ _ (ξ.val W hW w)))

/-- **The `T`-points of `Proj_Z(g^*𝒜)` are the `T`-points of `Z ×_X F`.**

A morphism `s : T ⟶ Proj_Z(g^*𝒜)` over `S` is sent to its composite `t` with the structure
morphism together with the point `AlgebraicGeometry.Space.GradedAlgebraRestriction.projPoint` of
`F(T)` over `g ∘ t`. -/
def projEquiv {Z : BigFppfOver B S hS} (g : yoneda.obj Z ⟶ X)
    (hc : B.Contains (relativeProj (Â Z g)).scheme) (T : BigFppfOver B S hS) :
    (T ⟶ projObj Â g hc) ≃
      {p : (T ⟶ Z) × LimPoint ρ T // p.2.point = yoneda.map p.1 ≫ g} where
  toFun s := ⟨(s ≫ projHom Â g hc, ρ.projPoint g hc s), rfl⟩
  invFun p := ρ.projHomOf g hc p.1.1 p.1.2 p.2
  left_inv s := ρ.projHomOf_projPoint g hc s
  right_inv p := Subtype.ext (Prod.ext (ρ.projHomOf_comp_projHom g hc p.1.1 p.1.2 p.2)
    (ρ.projPoint_projHomOf g hc p.1.1 p.1.2 p.2))

/-- `projEquiv g hc T` sends `s` to its composite with the structure morphism together with
`projPoint g hc s`. -/
@[simp] theorem projEquiv_apply {Z : BigFppfOver B S hS} (g : yoneda.obj Z ⟶ X)
    (hc : B.Contains (relativeProj (Â Z g)).scheme) {T : BigFppfOver B S hS}
    (s : T ⟶ projObj Â g hc) :
    (ρ.projEquiv g hc T s).1 = (s ≫ projHom Â g hc, ρ.projPoint g hc s) := rfl

/-- **The point of `Z ×_X F` attached to a `T`-point of `Proj_Z(g^*𝒜)` is natural in the test
object**: restricting the `T`-point along `u : T' ⟶ T` restricts the point of `F(T)`. -/
theorem projPoint_comp {Z : BigFppfOver B S hS} (g : yoneda.obj Z ⟶ X)
    (hc : B.Contains (relativeProj (Â Z g)).scheme) {T T' : BigFppfOver B S hS} (u : T' ⟶ T)
    (s : T ⟶ projObj Â g hc) :
    ρ.projPoint g hc (u ≫ s) = (ρ.projPoint g hc s).restrict u := by
  refine LimPoint.ext' rfl fun W hW w => ?_
  refine ρ.fibreOfF_heq g _ _ (homEquiv_val_fst _ _ _ _ _) (homEquiv_val_fst _ _ _ _ _) rfl rfl ?_
  exact congrArg (fun z : Scheme.QcExtension (F.functor (situationAlgebra (Â Z g)))
      ((BigFppfOver.toScheme B S hS).obj T') => z.val _ hW ((BigFppfOver.toScheme B S hS).map w))
    ((relativeProjRepresentableByFunctorUnconditional (Â Z g)).homEquiv_comp
      ((BigFppfOver.toScheme B S hS).map u)
      ((BigFppfOver.toScheme B S hS).map s :
        (BigFppfOver.toScheme B S hS).obj T ⟶ (relativeProj (Â Z g)).scheme))

end GradedAlgebraRestriction

end AlgebraicGeometry.Space

end
