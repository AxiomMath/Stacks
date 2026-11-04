module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.GaloisCoverDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.GaloisTrivializationExists
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricFrobeniusClosedPoint
public import StacksFrontier.Algebra.Module.Projective.Determinant.CharSeries
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The stalk of a descent sheaf at a geometric point

Let `C` be a Galois covering `A ⟶ X` with group `H` and `D(N)` the descent sheaf of a `Λ`-module
`N` with an action `ρ` of `H`, whose sections over an étale `W ⟶ X` are the `H`-equivariant
locally constant maps `W ×_X A → N`. For a geometric point `x` of `X` and a point `a` of `A` over
it, the stalk of `D(N)` at `x` is `N`: the germ of an equivariant map goes to its value at the
point `(w, a)` of `W ×_X A`, where `w` is the point of the neighbourhood `W` over `x`.

An endomorphism `σ` of the geometric point `x` moves `a` to another point of `A` over `x`. Two
such points differ by a unique element of `H`, so `σ` has a group element `g`, defined by
`σ ∘ a ∘ (act g) = a`. On the stalk, `σ` acts as `ρ g`. For the geometric Frobenius at a point
with finite residue field, `g` is the Frobenius element of `a`, and the geometric Frobenius on
the stalk of `D(N)` is `ρ g`.

## Main definitions

* `AlgebraicGeometry.EtaleGaloisCovering.pointElement`: the group element of an endomorphism
  of a geometric point at a point of the covering over it.
* `AlgebraicGeometry.EtaleGaloisCovering.stalkLinearEquiv`: the stalk of the descent sheaf at a
  geometric point, identified with the module by evaluation at a point of the covering.

## Main results

* `AlgebraicGeometry.EtaleGaloisCovering.exists_lift_geometricPoint` and
  `.exists_lift_geometricPointAt`: every geometric point lifts to the covering.
* `AlgebraicGeometry.EtaleGaloisCovering.exists_comp_act_eq_of_field`: two points of the covering
  with values in a field, over the same point of `X`, differ by an element of the group.
* `AlgebraicGeometry.EtaleGaloisCovering.stalkLinearEquiv_sheafFiber_map`: an endomorphism of
  the geometric point acts on the stalk as its group element.
* `AlgebraicGeometry.EtaleGaloisCovering.stalkLinearEquiv_frobeniusStalk`: the geometric
  Frobenius acts on the stalk as the Frobenius element.
* `AlgebraicGeometry.EtaleGaloisCovering.pointElement_comp_act` and
  `.pointElement_comp_eq_pow`: the group element under a change of the point of the covering, and
  along a morphism of geometric points intertwining an endomorphism with a power of another.
* `AlgebraicGeometry.EtaleGaloisCovering.stalkLinearEquivOfIso_frobeniusStalk` and
  `.charSeries_frobeniusStalk_eq`: the same for a sheaf isomorphic to a descent sheaf, and the
  local factor `det(1 - Frob T^d)` on the stalk is that of `ρ g`.

## References

* [Stacks Project, Tag 03UZ](https://stacks.math.columbia.edu/tag/03UZ)
* [Stacks Project, Tag 0GIY](https://stacks.math.columbia.edu/tag/0GIY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u r w v

namespace AlgebraicGeometry.EtaleGaloisCovering

variable {X : Scheme.{u}} {H : Type w} [Group H] (C : EtaleGaloisCovering X H)

/-- **Two points of a Galois covering over the same point differ by an element of the group.** Two
morphisms from the spectrum of a field into the covering with the same composite to `X` differ by
the action of an element of the group. -/
public theorem exists_comp_act_eq_of_field {K : Type u} [Field K]
    (a b : Spec (.of K) ⟶ C.cover.left) (hab : a ≫ C.cover.hom = b ≫ C.cover.hom) :
    ∃ h : H, a ≫ C.act h = b := by
  obtain ⟨h, hw, hmem⟩ := C.exists_mem_agreeLocus a b hab default
  let O := Scheme.Hom.agreeLocus C.cover.hom (a ≫ C.act h) b hw
  have : Surjective O.ι := ⟨fun y => ⟨⟨y, Subsingleton.elim y default ▸ hmem⟩, rfl⟩⟩
  have : IsIso O.ι :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, inferInstance⟩
  refine ⟨h, (cancel_epi O.ι).mp ?_⟩
  rw [← Category.assoc]
  exact Scheme.Hom.agreeLocus_ι_comp C.cover.hom (a ≫ C.act h) b hw

/-- The element of the group in `C.exists_comp_act_eq_of_field` is unique. -/
public theorem eq_of_comp_act_eq_of_field {K : Type u} [Field K]
    (a : Spec (.of K) ⟶ C.cover.left) {h h' : H} (hh : a ≫ C.act h = a ≫ C.act h') : h = h' :=
  C.eq_of_comp_eq a hh

/-- **Geometric points lift to the covering.** Every geometric point of `X` factors through the
covering. -/
public theorem exists_lift_geometricPoint (x : GeometricPoint X) :
    ∃ a : x.source ⟶ C.cover.left, a ≫ C.cover.hom = x.hom := by
  obtain ⟨y, hy⟩ := C.surjective (x.hom default)
  obtain ⟨a, ha, -⟩ := Scheme.exists_fac_of_etale_of_isSepClosed C.cover.hom x.hom y hy
  exact ⟨a, ha⟩

/-- **The geometric point at a point lifts to the covering.** -/
public theorem exists_lift_geometricPointAt (y : X) :
    ∃ a : (Stacks.Frobenius.geometricPointAt X y).source ⟶ C.cover.left,
      a ≫ C.cover.hom = (Stacks.Frobenius.geometricPointAt X y).hom :=
  C.exists_lift_geometricPoint _

variable {x : GeometricPoint X}

/-- **The group element of an endomorphism of a geometric point.** Given a point `a` of the
covering over the geometric point `x` and an endomorphism `σ` of `x`, this is the unique element
`g` of the group such that translating `σ ∘ a` by `g` gives back `a`. -/
public def pointElement (a : x.source ⟶ C.cover.left) (ha : a ≫ C.cover.hom = x.hom)
    (σ : GeometricPoint.Hom x x) : H :=
  (C.exists_comp_act_eq_of_field (σ.hom ≫ a) a
    (by rw [Category.assoc, ha, σ.comm])).choose

/-- The defining equation of the group element: `σ ∘ a ∘ (act g) = a` for
`g = C.pointElement a ha σ`. -/
public theorem comp_act_pointElement (a : x.source ⟶ C.cover.left)
    (ha : a ≫ C.cover.hom = x.hom) (σ : GeometricPoint.Hom x x) :
    σ.hom ≫ a ≫ C.act (C.pointElement a ha σ) = a := by
  rw [← Category.assoc]
  exact (C.exists_comp_act_eq_of_field (σ.hom ≫ a) a
    (by rw [Category.assoc, ha, σ.comm])).choose_spec

/-- The group element of `σ` is characterized by its defining equation. -/
public theorem pointElement_eq_of_comp_act (a : x.source ⟶ C.cover.left)
    (ha : a ≫ C.cover.hom = x.hom) {σ : GeometricPoint.Hom x x} {g : H}
    (hg : σ.hom ≫ a ≫ C.act g = a) : C.pointElement a ha σ = g :=
  C.eq_of_comp_eq (σ.hom ≫ a) (by
    rw [Category.assoc, Category.assoc, C.comp_act_pointElement a ha σ, hg])

/-- **Changing the point of the covering conjugates the group element.** Replacing `a` by its
translate `a ∘ (act k)` replaces the group element `g` of `σ` by `k g k⁻¹`. -/
public theorem pointElement_comp_act (a : x.source ⟶ C.cover.left)
    (ha : a ≫ C.cover.hom = x.hom) (k : H) (σ : GeometricPoint.Hom x x) :
    C.pointElement (a ≫ C.act k) (by rw [Category.assoc, C.act_comp_hom', ha]) σ =
      k * C.pointElement a ha σ * k⁻¹ := by
  refine C.pointElement_eq_of_comp_act _ _ ?_
  have e : C.act k ≫ C.act (k * C.pointElement a ha σ * k⁻¹) =
      C.act (C.pointElement a ha σ) ≫ C.act k := by
    rw [← C.act_mul, ← C.act_mul]
    congr 1
    group
  rw [Category.assoc, e, ← Category.assoc a, ← Category.assoc σ.hom, C.comp_act_pointElement]

/-- **Powers.** If `s ∘ a ∘ (act g) = a` for an endomorphism `s` of the source of `x`, then
`sⁿ ∘ a ∘ (act gⁿ) = a`. -/
public theorem pow_comp_act_pow {s : End x.source} {g : H} (a : x.source ⟶ C.cover.left)
    (hs : s ≫ a ≫ C.act g = a) (n : ℕ) : (s ^ n : End x.source) ≫ a ≫ C.act (g ^ n) = a := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, C.act_one]
    exact (Category.id_comp _).trans (Category.comp_id _)
  | succ n ih =>
    rw [pow_succ, End.mul_def, pow_succ', C.act_mul, Category.assoc,
      ← Category.assoc a, ← Category.assoc (s ^ n : End x.source), ih, hs]

/-- **Compatibility of group elements along a morphism of geometric points.** Let `j : y ⟶ x` be
a morphism of geometric points, `τ` an endomorphism of `y` and `σ` one of `x` with
`τ ∘ j = j ∘ σⁿ`. Then the group element of `τ` at the point `j ≫ a` is the `n`-th power of the
group element of `σ` at `a`. -/
public theorem pointElement_comp_eq_pow {y : GeometricPoint X} (j : GeometricPoint.Hom y x)
    (a : x.source ⟶ C.cover.left) (ha : a ≫ C.cover.hom = x.hom)
    (τ : GeometricPoint.Hom y y) (σ : GeometricPoint.Hom x x) (n : ℕ)
    (h : τ.hom ≫ j.hom = j.hom ≫ End.asHom (End.of σ.hom ^ n)) :
    C.pointElement (j.hom ≫ a) (by rw [Category.assoc, ha, j.comm]) τ =
      C.pointElement a ha σ ^ n := by
  refine C.pointElement_eq_of_comp_act _ _ ?_
  rw [Category.assoc, ← Category.assoc τ.hom, h, Category.assoc,
    C.pow_comp_act_pow a (C.comp_act_pointElement a ha σ) n]

/-! ### The stalk -/

/-- The point of `W ×_X A` given by a point `p` of an étale `X`-scheme `W` over `x` and the chosen
point `a` of the covering over `x`. -/
public def liftPoint (a : x.source ⟶ C.cover.left) (ha : a ≫ C.cover.hom = x.hom) {W : X.Etale}
    (p : (Scheme.pointSmallEtale x.hom).fiber.obj W) : x.source ⟶ C.fiberProd W :=
  pullback.lift p.left a (by rw [ha]; exact Over.w p)

/-- The first projection of `C.liftPoint a ha p` is the point `p` of `W`. -/
@[reassoc (attr := simp)]
public theorem liftPoint_fst (a : x.source ⟶ C.cover.left) (ha : a ≫ C.cover.hom = x.hom)
    {W : X.Etale} (p : (Scheme.pointSmallEtale x.hom).fiber.obj W) :
    C.liftPoint a ha p ≫ pullback.fst _ _ = p.left :=
  pullback.lift_fst _ _ _

/-- The second projection of `C.liftPoint a ha p` is `a`. -/
@[reassoc (attr := simp)]
public theorem liftPoint_snd (a : x.source ⟶ C.cover.left) (ha : a ≫ C.cover.hom = x.hom)
    {W : X.Etale} (p : (Scheme.pointSmallEtale x.hom).fiber.obj W) :
    C.liftPoint a ha p ≫ pullback.snd _ _ = a :=
  pullback.lift_snd _ _ _

/-- `liftPoint` commutes with the maps `W ×_X A ⟶ W' ×_X A` induced by morphisms `W ⟶ W'`. -/
public theorem liftPoint_pullbackMap (a : x.source ⟶ C.cover.left)
    (ha : a ≫ C.cover.hom = x.hom) {W W' : X.Etale} (g : W ⟶ W')
    (p : (Scheme.pointSmallEtale x.hom).fiber.obj W) :
    C.liftPoint a ha p ≫ C.pullbackMap g =
      C.liftPoint a ha ((Scheme.pointSmallEtale x.hom).fiber.map g p) := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullbackMap_fst, liftPoint_fst_assoc, liftPoint_fst]
    rfl
  · rw [Category.assoc, pullbackMap_snd, liftPoint_snd, liftPoint_snd]

variable (Λ : Type r) [Ring Λ] (N : Type (max (u + 1) v)) [AddCommGroup N] [Module Λ N]
  (ρ : H →* Module.End Λ N)

/-- Evaluation of an equivariant map at the point `liftPoint a ha p`. -/
public def stalkEval (a : x.source ⟶ C.cover.left) (ha : a ≫ C.cover.hom = x.hom) {W : X.Etale}
    (p : (Scheme.pointSmallEtale x.hom).fiber.obj W) :
    (C.descentSheaf Λ N ρ).obj.obj (op W) ⟶ ModuleCat.of Λ N :=
  ModuleCat.ofHom
    { toFun f := f.1 ((C.liftPoint a ha p).base default)
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }

/-- `C.stalkEval Λ N ρ a ha p` evaluates an equivariant map at `C.liftPoint a ha p`. -/
public theorem stalkEval_apply (a : x.source ⟶ C.cover.left) (ha : a ≫ C.cover.hom = x.hom)
    {W : X.Etale} (p : (Scheme.pointSmallEtale x.hom).fiber.obj W)
    (f : (C.descentSheaf Λ N ρ).obj.obj (op W)) :
    C.stalkEval Λ N ρ a ha p f = f.1 ((C.liftPoint a ha p).base default) :=
  rfl

/-- **The stalk of the descent sheaf at `x`, evaluated at `a`.** The germ at `x` of an
equivariant map `W ×_X A → N` goes to its value at the point given by the point of `W` and the
point `a` of the covering. -/
public def stalkToModule (a : x.source ⟶ C.cover.left) (ha : a ≫ C.cover.hom = x.hom) :
    (Scheme.pointSmallEtale x.hom).presheafFiber.obj (C.descentSheaf Λ N ρ).obj ⟶
      ModuleCat.of Λ N :=
  (Scheme.pointSmallEtale x.hom).presheafFiberDesc (fun W p => C.stalkEval Λ N ρ a ha (W := W) p)
    (fun W W' g p => by
      refine ModuleCat.hom_ext (LinearMap.ext fun f => ?_)
      change f.1 ((C.pullbackMap g).base ((C.liftPoint a ha p).base default)) = _
      rw [← Scheme.Hom.comp_apply, liftPoint_pullbackMap]
      rfl)

/-- On the sections over `W`, `C.stalkToModule Λ N ρ a ha` is `C.stalkEval Λ N ρ a ha p`. -/
@[reassoc]
public theorem toPresheafFiber_stalkToModule (a : x.source ⟶ C.cover.left)
    (ha : a ≫ C.cover.hom = x.hom) {W : X.Etale} (p : (Scheme.pointSmallEtale x.hom).fiber.obj W) :
    (Scheme.pointSmallEtale x.hom).toPresheafFiber W p (C.descentSheaf Λ N ρ).obj ≫
        C.stalkToModule Λ N ρ a ha = C.stalkEval Λ N ρ a ha p :=
  (Scheme.pointSmallEtale x.hom).toPresheafFiber_presheafFiberDesc _ _ W p

/-- The germ at `x` of a section `f` over `W` goes to the value of `f` at `C.liftPoint a ha p`. -/
public theorem stalkToModule_toPresheafFiber_apply (a : x.source ⟶ C.cover.left)
    (ha : a ≫ C.cover.hom = x.hom) {W : X.Etale} (p : (Scheme.pointSmallEtale x.hom).fiber.obj W)
    (f : (C.descentSheaf Λ N ρ).obj.obj (op W)) :
    C.stalkToModule Λ N ρ a ha
        ((Scheme.pointSmallEtale x.hom).toPresheafFiber W p (C.descentSheaf Λ N ρ).obj f) =
      f.1 ((C.liftPoint a ha p).base default) :=
  ConcreteCategory.congr_hom (C.toPresheafFiber_stalkToModule Λ N ρ a ha p) f

/-- Moving the point of `W` by an endomorphism `σ` of the geometric point moves the point of
`W ×_X A` by the group element of `σ`. -/
public theorem liftPoint_fiber_map (a : x.source ⟶ C.cover.left) (ha : a ≫ C.cover.hom = x.hom)
    (σ : GeometricPoint.Hom x x) {W : X.Etale} (p : (Scheme.pointSmallEtale x.hom).fiber.obj W) :
    σ.hom ≫ C.liftPoint a ha p ≫ C.pullbackAct W (C.pointElement a ha σ) =
      C.liftPoint a ha ((smallEtalePointHom X σ).hom.app W p) := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, pullbackAct_fst, liftPoint_fst, liftPoint_fst]
    rfl
  · rw [Category.assoc, Category.assoc, pullbackAct_snd, liftPoint_snd_assoc, liftPoint_snd,
      C.comp_act_pointElement a ha σ]

/-- **An endomorphism of the geometric point acts on the stalk of the descent sheaf through its
group element.** Under evaluation at `a`, the action on the stalk of an endomorphism `σ` of the
geometric point `x` is the action of the group element `C.pointElement a ha σ` on `N`. -/
public theorem presheafFiber_smallEtalePointHom_comp_stalkToModule (a : x.source ⟶ C.cover.left)
    (ha : a ≫ C.cover.hom = x.hom) (σ : GeometricPoint.Hom x x) :
    (GrothendieckTopology.Point.Hom.presheafFiber (smallEtalePointHom X σ)).app
        (C.descentSheaf Λ N ρ).obj ≫ C.stalkToModule Λ N ρ a ha =
      C.stalkToModule Λ N ρ a ha ≫ ModuleCat.ofHom (ρ (C.pointElement a ha σ)) := by
  refine (Scheme.pointSmallEtale x.hom).presheafFiber_hom_ext fun W p => ?_
  have hσ : (Scheme.pointSmallEtale x.hom).toPresheafFiber W p (C.descentSheaf Λ N ρ).obj ≫
      (GrothendieckTopology.Point.Hom.presheafFiber (smallEtalePointHom X σ)).app
        (C.descentSheaf Λ N ρ).obj =
      (Scheme.pointSmallEtale x.hom).toPresheafFiber W ((smallEtalePointHom X σ).hom.app W p)
        (C.descentSheaf Λ N ρ).obj := by
    rw [GrothendieckTopology.Point.Hom.presheafFiber_app]
    exact (Scheme.pointSmallEtale x.hom).toPresheafFiber_presheafFiberDesc _ _ W p
  rw [reassoc_of% hσ, toPresheafFiber_stalkToModule, toPresheafFiber_stalkToModule_assoc]
  refine ModuleCat.hom_ext (LinearMap.ext fun f => ?_)
  show f.1 ((C.liftPoint a ha _).base default) =
    ρ (C.pointElement a ha σ) (f.1 ((C.liftPoint a ha p).base default))
  rw [← liftPoint_fiber_map, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply,
    Subsingleton.elim (σ.hom.base default) default]
  exact f.2 _ _

/-- At a point of `W` over `a`, for `W` over the covering, evaluation at `a` is evaluation of the
restriction to the graph. -/
public theorem liftPoint_eq_comp_graph (a : x.source ⟶ C.cover.left)
    (ha : a ≫ C.cover.hom = x.hom) (T : Over C.cover)
    (p : (Scheme.pointSmallEtale x.hom).fiber.obj T.left) (hp : p.left ≫ T.hom.left = a) :
    C.liftPoint a ha p = p.left ≫ C.graph T := by
  apply pullback.hom_ext
  · exact (C.liftPoint_fst a ha p).trans (((Category.assoc _ _ _).trans
      ((congrArg (p.left ≫ ·) (C.graph_fst T)).trans (Category.comp_id _))).symm)
  · exact (C.liftPoint_snd a ha p).trans (((Category.assoc _ _ _).trans
      ((congrArg (p.left ≫ ·) (C.graph_snd T)).trans hp)).symm)

/-- Restriction to the graph commutes with restriction along a morphism over the covering. -/
public theorem restrictGraph_map {T T' : Over C.cover} (k : T' ⟶ T)
    (f : (C.descentSheaf Λ N ρ).obj.obj (op T.left)) :
    C.restrictGraph Λ N ρ T' ((C.descentSheaf Λ N ρ).obj.map k.left.op f) =
      (C.restrictGraph Λ N ρ T f).comap k.left.left.base.hom := by
  refine LocallyConstant.ext fun y => ?_
  show f.1 ((C.pullbackMap k.left).base ((C.graph T').base y)) =
    f.1 ((C.graph T).base (k.left.left.base y))
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, C.graph_naturality k]

/-- The point `a` of the covering, as a point of the covering over `x`. -/
public def coverPoint (a : x.source ⟶ C.cover.left) (ha : a ≫ C.cover.hom = x.hom) :
    (Scheme.pointSmallEtale x.hom).fiber.obj C.cover :=
  Over.homMk a ha

/-- **Evaluation at `a` is surjective on the stalk.** -/
public theorem surjective_stalkToModule (a : x.source ⟶ C.cover.left)
    (ha : a ≫ C.cover.hom = x.hom) : Function.Surjective (C.stalkToModule Λ N ρ a ha) := by
  intro n
  let T : Over C.cover := Over.mk (𝟙 C.cover)
  obtain ⟨f, hf⟩ := (C.bijective_restrictGraph Λ N ρ T).2 (LocallyConstant.const _ n)
  refine ⟨(Scheme.pointSmallEtale x.hom).toPresheafFiber C.cover (C.coverPoint a ha)
    (C.descentSheaf Λ N ρ).obj f, ?_⟩
  refine (C.stalkToModule_toPresheafFiber_apply Λ N ρ a ha (C.coverPoint a ha) f).trans ?_
  have hL : C.liftPoint a ha (C.coverPoint a ha) = a ≫ C.graph T :=
    C.liftPoint_eq_comp_graph a ha T (C.coverPoint a ha) (Category.comp_id _)
  rw [hL, Scheme.Hom.comp_apply]
  exact congrArg (fun c : LocallyConstant _ N => c (a.base default)) hf

/-- **Evaluation at `a` is injective on the stalk.** -/
public theorem injective_stalkToModule (a : x.source ⟶ C.cover.left)
    (ha : a ≫ C.cover.hom = x.hom) : Function.Injective (C.stalkToModule Λ N ρ a ha) := by
  let Φ := Scheme.pointSmallEtale x.hom
  let D := (C.descentSheaf Λ N ρ).obj
  have : PreservesColimitsOfSize.{u, u}
      (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{max (u + 1) v, r, u, u} Λ
  have : PreservesFilteredColimitsOfSize.{u, u} (forget AddCommGrpCat.{max (u + 1) v}) :=
    preservesFilteredColimitsOfSize_of_univLE.{max (u + 1) v, max (u + 1) v, u, u} _
  have : PreservesFilteredColimitsOfSize.{u, u} (forget (ModuleCat.{max (u + 1) v} Λ)) := by
    show PreservesFilteredColimitsOfSize
      (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v} ⋙
        forget AddCommGrpCat.{max (u + 1) v})
    infer_instance
  refine (injective_iff_map_eq_zero (C.stalkToModule Λ N ρ a ha).hom).mpr fun z hz => ?_
  obtain ⟨W, p, f, rfl⟩ := Φ.toPresheafFiber_jointly_surjective z
  have hz' : f.1 ((C.liftPoint a ha p).base default) = 0 :=
    (C.stalkToModule_toPresheafFiber_apply Λ N ρ a ha p f).symm.trans hz
  let W₁ := C.fiberObj W
  let p₁ : Φ.fiber.obj W₁ := Over.homMk (C.liftPoint a ha p) (by
    show C.liftPoint a ha p ≫ pullback.fst _ _ ≫ W.hom = x.hom
    rw [liftPoint_fst_assoc]
    exact Over.w p)
  have hp₁ : Φ.fiber.map (C.fiberObjFst W) p₁ = p :=
    Over.OverMorphism.ext (C.liftPoint_fst a ha p)
  let f₁ := D.map (C.fiberObjFst W).op f
  have h₁ : Φ.toPresheafFiber W p D f = Φ.toPresheafFiber W₁ p₁ D f₁ := by
    rw [← hp₁, GrothendieckTopology.Point.toPresheafFiber_w_apply]
  let T₁ : Over C.cover := Over.mk (C.fiberObjSnd W)
  let c := C.restrictGraph Λ N ρ T₁ f₁
  have hc : c (p₁.left.base (default : x.source)) = 0 := by
    have hL := C.liftPoint_eq_comp_graph a ha T₁ p₁ (C.liftPoint_snd a ha p)
    have hL' : C.liftPoint a ha p₁ ≫ C.pullbackMap (C.fiberObjFst W) = C.liftPoint a ha p := by
      rw [liftPoint_pullbackMap, hp₁]
    have e := congrArg (fun m => m.base (default : x.source))
      ((congrArg (· ≫ C.pullbackMap (C.fiberObjFst W)) hL.symm).trans hL')
    exact (congrArg (fun z => f.1 z) e).trans hz'
  let O : W₁.left.Opens := ⟨c ⁻¹' {0}, c.isLocallyConstant.isOpen_fiber 0⟩
  have : IsOpenImmersion O.ι := inferInstanceAs (IsOpenImmersion (Scheme.Opens.ι O))
  let W₂ := etaleOfOpens W₁ O
  let ι₂ := etaleOfOpensι W₁ O
  have hrange : Set.range (C.liftPoint a ha p).base ⊆ Set.range O.ι.base := by
    rintro _ ⟨y, rfl⟩
    rw [show y = (default : x.source) from Subsingleton.elim (α := x.source) y default]
    exact ⟨⟨_, hc⟩, rfl⟩
  let q₂ : x.source ⟶ O.toScheme := IsOpenImmersion.lift O.ι (C.liftPoint a ha p) hrange
  have hq₂ : q₂ ≫ O.ι = C.liftPoint a ha p := IsOpenImmersion.lift_fac _ _ _
  let p₂ : Φ.fiber.obj W₂ := Over.homMk q₂ (by
    show q₂ ≫ O.ι ≫ pullback.fst _ _ ≫ W.hom = x.hom
    rw [reassoc_of% hq₂]
    exact (C.liftPoint_fst_assoc a ha p W.hom).trans (Over.w p))
  have hp₂ : Φ.fiber.map ι₂ p₂ = p₁ := Over.OverMorphism.ext hq₂
  have h₂ : Φ.toPresheafFiber W₁ p₁ D f₁ = Φ.toPresheafFiber W₂ p₂ D (D.map ι₂.op f₁) := by
    have := Φ.toPresheafFiber_w_apply ι₂ p₂ D f₁
    rw [hp₂] at this
    exact this.symm
  let T₂ : Over C.cover := Over.mk (ι₂ ≫ C.fiberObjSnd W)
  let k : T₂ ⟶ T₁ := Over.homMk ι₂ rfl
  have h₃ : D.map ι₂.op f₁ = 0 := by
    refine (C.bijective_restrictGraph Λ N ρ T₂).1 ?_
    refine (C.restrictGraph_map Λ N ρ k f₁).trans ((LocallyConstant.ext fun y => y.2).trans
      (map_zero (C.restrictGraph Λ N ρ T₂)).symm)
  rw [h₁, h₂, h₃, map_zero]

/-- **The stalk of a descent sheaf is the module.** Evaluation at a point `a` of the covering
over the geometric point `x` identifies the stalk at `x` of the descent sheaf of `N` with `N`. -/
public def stalkLinearEquiv (a : x.source ⟶ C.cover.left) (ha : a ≫ C.cover.hom = x.hom) :
    ((Scheme.pointSmallEtale x.hom).sheafFiber (A := ModuleCat.{max (u + 1) v} Λ)).obj
      (C.descentSheaf Λ N ρ) ≃ₗ[Λ] N :=
  LinearEquiv.ofBijective (C.stalkToModule Λ N ρ a ha).hom
    ⟨C.injective_stalkToModule Λ N ρ a ha, C.surjective_stalkToModule Λ N ρ a ha⟩

/-- `C.stalkLinearEquiv Λ N ρ a ha` is `C.stalkToModule Λ N ρ a ha`. -/
public theorem stalkLinearEquiv_apply (a : x.source ⟶ C.cover.left)
    (ha : a ≫ C.cover.hom = x.hom)
    (m : ((Scheme.pointSmallEtale x.hom).sheafFiber (A := ModuleCat.{max (u + 1) v} Λ)).obj
      (C.descentSheaf Λ N ρ)) :
    C.stalkLinearEquiv Λ N ρ a ha m = C.stalkToModule Λ N ρ a ha m :=
  rfl

/-- **An endomorphism of the geometric point acts on the stalk of a descent sheaf as its group
element.** Under `stalkLinearEquiv`, the action on the stalk at `x` of an endomorphism `σ` of
`x` is `ρ g` for the group element `g = C.pointElement a ha σ`, defined by
`σ ∘ a ∘ (act g) = a`. -/
@[sga "5 X 6.1" "(6.1.1)"]
public theorem stalkLinearEquiv_sheafFiber_map (a : x.source ⟶ C.cover.left)
    (ha : a ≫ C.cover.hom = x.hom) (σ : GeometricPoint.Hom x x)
    (m : ((Scheme.pointSmallEtale x.hom).sheafFiber (A := ModuleCat.{max (u + 1) v} Λ)).obj
      (C.descentSheaf Λ N ρ)) :
    C.stalkLinearEquiv Λ N ρ a ha
        (((GrothendieckTopology.Point.Hom.sheafFiber (smallEtalePointHom X σ)).app
          (C.descentSheaf Λ N ρ)).hom m) =
      ρ (C.pointElement a ha σ) (C.stalkLinearEquiv Λ N ρ a ha m) :=
  ConcreteCategory.congr_hom
    (C.presheafFiber_smallEtalePointHom_comp_stalkToModule Λ N ρ a ha σ) m

/-- **The geometric Frobenius on the stalk of a descent sheaf at a point with finite residue
field.** At the geometric point `geometricPointAt X x` of a point `x` with finite residue field,
the geometric Frobenius on the stalk of the descent sheaf of `N` is `ρ g_x`, where
`g_x = C.pointElement a ha (frobeniusPointHom X x)` is the Frobenius element of the point `a`
of the covering over the geometric point. -/
public theorem stalkLinearEquiv_frobeniusStalk (y : X) [Finite (X.residueField y)]
    (a : (Stacks.Frobenius.geometricPointAt X y).source ⟶ C.cover.left)
    (ha : a ≫ C.cover.hom = (Stacks.Frobenius.geometricPointAt X y).hom)
    (m : ((Scheme.pointSmallEtale (Stacks.Frobenius.geometricPointAt X y).hom).sheafFiber
      (A := ModuleCat.{max (u + 1) v} Λ)).obj (C.descentSheaf Λ N ρ)) :
    C.stalkLinearEquiv Λ N ρ a ha
        ((Stacks.Frobenius.frobeniusStalk (ModuleCat.{max (u + 1) v} Λ) X y
          (C.descentSheaf Λ N ρ)).hom m) =
      ρ (C.pointElement a ha (Stacks.Frobenius.frobeniusPointHom X y))
        (C.stalkLinearEquiv Λ N ρ a ha m) :=
  C.stalkLinearEquiv_sheafFiber_map Λ N ρ a ha _ m

/-! ### Transport along an isomorphism with a descent sheaf -/

section Transport

variable {F : Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) v} Λ)}

/-- The stalk at `x` of a sheaf isomorphic to the descent sheaf of `N` is `N`. -/
public def stalkLinearEquivOfIso (e : F ≅ C.descentSheaf Λ N ρ) (a : x.source ⟶ C.cover.left)
    (ha : a ≫ C.cover.hom = x.hom) :
    ((Scheme.pointSmallEtale x.hom).sheafFiber (A := ModuleCat.{max (u + 1) v} Λ)).obj F ≃ₗ[Λ]
      N :=
  ((Scheme.pointSmallEtale x.hom).sheafFiber.mapIso e).toLinearEquiv.trans
    (C.stalkLinearEquiv Λ N ρ a ha)

/-- **An endomorphism of the geometric point acts on the stalk of a sheaf isomorphic to a descent
sheaf as its group element.** -/
public theorem stalkLinearEquivOfIso_sheafFiber_map (e : F ≅ C.descentSheaf Λ N ρ)
    (a : x.source ⟶ C.cover.left) (ha : a ≫ C.cover.hom = x.hom) (σ : GeometricPoint.Hom x x)
    (m : ((Scheme.pointSmallEtale x.hom).sheafFiber (A := ModuleCat.{max (u + 1) v} Λ)).obj F) :
    C.stalkLinearEquivOfIso Λ N ρ e a ha
        (((GrothendieckTopology.Point.Hom.sheafFiber (smallEtalePointHom X σ)).app F).hom m) =
      ρ (C.pointElement a ha σ) (C.stalkLinearEquivOfIso Λ N ρ e a ha m) := by
  show C.stalkLinearEquiv Λ N ρ a ha
      (((Scheme.pointSmallEtale x.hom).sheafFiber.map e.hom).hom
        (((GrothendieckTopology.Point.Hom.sheafFiber (smallEtalePointHom X σ)).app F).hom m)) = _
  rw [← ConcreteCategory.comp_apply,
    ← (GrothendieckTopology.Point.Hom.sheafFiber (smallEtalePointHom X σ)).naturality e.hom,
    ConcreteCategory.comp_apply, stalkLinearEquiv_sheafFiber_map]
  rfl

/-- **The geometric Frobenius on the stalk of a sheaf isomorphic to a descent sheaf** is the
Frobenius element. -/
public theorem stalkLinearEquivOfIso_frobeniusStalk (y : X) [Finite (X.residueField y)]
    {F : Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) v} Λ)} (e : F ≅ C.descentSheaf Λ N ρ)
    (a : (Stacks.Frobenius.geometricPointAt X y).source ⟶ C.cover.left)
    (ha : a ≫ C.cover.hom = (Stacks.Frobenius.geometricPointAt X y).hom)
    (m : ((Scheme.pointSmallEtale (Stacks.Frobenius.geometricPointAt X y).hom).sheafFiber
      (A := ModuleCat.{max (u + 1) v} Λ)).obj F) :
    C.stalkLinearEquivOfIso Λ N ρ e a ha
        ((Stacks.Frobenius.frobeniusStalk (ModuleCat.{max (u + 1) v} Λ) X y F).hom m) =
      ρ (C.pointElement a ha (Stacks.Frobenius.frobeniusPointHom X y))
        (C.stalkLinearEquivOfIso Λ N ρ e a ha m) :=
  C.stalkLinearEquivOfIso_sheafFiber_map Λ N ρ e a ha _ m

end Transport

/-! ### The local factor -/

section LocalFactor

variable {Λ : Type r} [CommRing Λ] {N : Type (max (u + 1) v)} [AddCommGroup N] [Module Λ N]
  [Module.Finite Λ N] [Module.Projective Λ N] {ρ : H →* Module.End Λ N}

/-- **The local factor of a sheaf isomorphic to a descent sheaf.** At a point `y` with finite
residue field, the characteristic series `det(1 - Frob_y T^d)` of the geometric Frobenius on the
stalk is that of `ρ g_y`, for the Frobenius element `g_y` of a point of the covering over the
geometric point at `y`. -/
public theorem charSeries_frobeniusStalk_eq (y : X) [Finite (X.residueField y)]
    {F : Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) v} Λ)} (e : F ≅ C.descentSheaf Λ N ρ)
    (a : (Stacks.Frobenius.geometricPointAt X y).source ⟶ C.cover.left)
    (ha : a ≫ C.cover.hom = (Stacks.Frobenius.geometricPointAt X y).hom)
    [Module.Finite Λ (((Scheme.pointSmallEtale
      (Stacks.Frobenius.geometricPointAt X y).hom).sheafFiber
      (A := ModuleCat.{max (u + 1) v} Λ)).obj F)]
    [Module.Projective Λ (((Scheme.pointSmallEtale
      (Stacks.Frobenius.geometricPointAt X y).hom).sheafFiber
      (A := ModuleCat.{max (u + 1) v} Λ)).obj F)] (d : ℕ) :
    ProjectiveDeterminant.charSeries
        (Stacks.Frobenius.frobeniusStalk (ModuleCat.{max (u + 1) v} Λ) X y F).hom d =
      ProjectiveDeterminant.charSeries (ρ (C.pointElement a ha
        (Stacks.Frobenius.frobeniusPointHom X y))) d := by
  let ε := C.stalkLinearEquivOfIso Λ N ρ e a ha
  have h : ε.conj (Stacks.Frobenius.frobeniusStalk (ModuleCat.{max (u + 1) v} Λ) X y F).hom =
      ρ (C.pointElement a ha (Stacks.Frobenius.frobeniusPointHom X y)) := by
    refine LinearMap.ext fun n => ?_
    obtain ⟨m, rfl⟩ := ε.surjective n
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
    exact C.stalkLinearEquivOfIso_frobeniusStalk Λ N ρ y e a ha m
  rw [← h, ProjectiveDeterminant.charSeries_conj]

end LocalFactor

end AlgebraicGeometry.EtaleGaloisCovering

end
