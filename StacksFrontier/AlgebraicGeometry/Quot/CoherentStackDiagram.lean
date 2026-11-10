module

public import StacksFrontier.AlgebraicGeometry.Quot.PicardDescent.BaseChange
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackSpanIso

/-!
# A diagram of objects of `Coh_{X/Y}` over a covering family, and its module descent datum

Let `D` be the standing datum of Stacks 08KB and let `{fP l : P_l ⟶ U}` be a covering family of
an object `U` of the big fppf site.  A *descent diagram* over it
(`AlgebraicGeometry.Space.CoherentDescentDiagram`) is the data the proof of Stacks 08KC extracts
from a descent datum for `Coh_{X/Y}`: objects `P l` of `Coh_{X/Y}` over the members, objects
`Q l m` over the pairwise fibre products with morphisms `c l m : Q l m ⟶ P l` and
`e l m : Q l m ⟶ P m`, and objects `T l m n` over the triple fibre products with morphisms to the
three `Q`s satisfying the three relations that express the cocycle condition.

This file performs the first two steps of the proof of the source.  First, the morphisms to the
base `Y` of the objects `P l` agree on the overlaps, so they glue to a morphism `g : U ⟶ Y`
(Descent on Spaces, Lemma 04P2, read here as the sheaf property of `Y`).  Second, writing
`X_l = X_{P l}` for the base changes and `a l : X_l ⟶ X_U` for the induced morphisms of base
changes, the modules of the `P l`, glued by the span isomorphisms of `c l m` and `e l m` on the
pairwise fibre products `X_l ×_{X_U} X_m`, form a descent datum for quasi-coherent modules
relative to `{a l}` (Stacks 04W3).

## Main definitions

* `AlgebraicGeometry.Space.CoherentDescentDiagram`: a descent diagram.
* `AlgebraicGeometry.Space.CoherentDescentDiagram.baseObject`: the test scheme `(U, g)` over `Y`,
  and `.toBase` the morphisms from the test schemes of the `P l` to it.
* `AlgebraicGeometry.Space.CoherentDescentDiagram.memberMap`: the morphisms `a l` of base
  changes.
* `AlgebraicGeometry.Space.CoherentDescentDiagram.pairLift`: the identification of the pairwise
  fibre product of the `X_l` with the base change of `Q l m`.
* `AlgebraicGeometry.Space.CoherentDescentDiagram.moduleDatum`: the descent datum of modules.

## References

* [Stacks Project, Tag 08KC](https://stacks.math.columbia.edu/tag/08KC)
* [Stacks Project, Tag 08KB](https://stacks.math.columbia.edu/tag/08KB)
* [Stacks Project, Tag 04P2](https://stacks.math.columbia.edu/tag/04P2)
* [Stacks Project, Tag 04W3](https://stacks.math.columbia.edu/tag/04W3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry.Space

open QuasiCoherentDescent (pullbackComparison pair pairFst pairSnd pair_condition DescentDatum
  transitionOn)

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A descent diagram for `Coh_{X/Y}` over a family `{fP l : P_l ⟶ U}`.**  Objects over the
members, over the pairwise fibre products and over the triple fibre products, joined by morphisms
whose base maps form the two cartesian squares of a covering, and subject to the three relations
which express the cocycle condition. -/
structure CoherentDescentDiagram (D : CoherentSituation B S hS) (U : BigFppfOver B S hS)
    (L : Type v) where
  /-- The objects over the members of the family. -/
  P : L → CoherentObject D
  /-- The members of the family. -/
  fP : ∀ l, (P l).T.left ⟶ U
  /-- The objects over the pairwise fibre products. -/
  Q : L → L → CoherentObject D
  /-- The morphisms to the first factor. -/
  c : ∀ l m, CoherentHom (Q l m) (P l)
  /-- The morphisms to the second factor. -/
  e : ∀ l m, CoherentHom (Q l m) (P m)
  /-- The base maps of `c` and `e` form a fibre product of `fP l` and `fP m`. -/
  sq₂ : ∀ l m, IsPullback (c l m).base.left (e l m).base.left (fP l) (fP m)
  /-- The objects over the triple fibre products. -/
  T : L → L → L → CoherentObject D
  /-- The morphisms to the first two factors. -/
  b₁₂ : ∀ l m n, CoherentHom (T l m n) (Q l m)
  /-- The morphisms to the last two factors. -/
  b₂₃ : ∀ l m n, CoherentHom (T l m n) (Q m n)
  /-- The morphisms to the outer two factors. -/
  b₁₃ : ∀ l m n, CoherentHom (T l m n) (Q l n)
  /-- The triple fibre product is the fibre product of two pairwise ones over the middle member. -/
  sq₃ : ∀ l m n, IsPullback (b₁₂ l m n).base.left (b₂₃ l m n).base.left (e l m).base.left
    (c m n).base.left
  /-- The first relation. -/
  hc₁ : ∀ l m n, (b₁₂ l m n).comp (c l m) = (b₁₃ l m n).comp (c l n)
  /-- The second relation. -/
  hc₂ : ∀ l m n, (b₁₂ l m n).comp (e l m) = (b₂₃ l m n).comp (c m n)
  /-- The third relation. -/
  hc₃ : ∀ l m n, (b₂₃ l m n).comp (e m n) = (b₁₃ l m n).comp (e l n)

/-- The morphism of base changes induced by a composite is the composite. -/
theorem CoherentSituation.relativeMap_comp (D : CoherentSituation B S hS)
    {T T' T'' : SchemesOver D.Y} (h : T ⟶ T') (h' : T' ⟶ T'') :
    D.relativeMap (h ≫ h') = D.relativeMap h ≫ D.relativeMap h' :=
  baseChangeMap_comp D.f h h'

namespace CoherentDescentDiagram

variable {D : CoherentSituation B S hS} {U : BigFppfOver B S hS} {L : Type v}
  (Δ : CoherentDescentDiagram D U L)

/-! ### The base map -/

/-- The morphisms of the objects over the members to `Y` agree on the overlaps. -/
theorem compatible_base {Z : BigFppfOver B S hS} (l m : L) (a : Z ⟶ (Δ.P l).T.left)
    (a' : Z ⟶ (Δ.P m).T.left) (h : a ≫ Δ.fP l = a' ≫ Δ.fP m) :
    (schemeSpaceFunctor B S hS).map a ≫ (Δ.P l).T.hom =
      (schemeSpaceFunctor B S hS).map a' ≫ (Δ.P m).T.hom := by
  obtain ⟨k, hk₁, hk₂⟩ := (Δ.sq₂ l m).exists_lift a a' h
  rw [← hk₁, ← hk₂, Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
    CostructuredArrow.w (Δ.c l m).base, CostructuredArrow.w (Δ.e l m).base]

/-- **The morphisms of the objects over the members to `Y` glue.**  Over a covering family the
compatible family of morphisms to the algebraic space `Y` comes from a morphism `U ⟶ Y`, because
an algebraic space is a sheaf for the fppf topology. -/
theorem exists_baseMap (hcov : Sieve.ofArrows (fun l => (Δ.P l).T.left) Δ.fP ∈
      BigFppfOver.topology B S hS U) :
    ∃ g : (schemeSpaceFunctor B S hS).obj U ⟶ D.Y,
      ∀ l, (schemeSpaceFunctor B S hS).map (Δ.fP l) ≫ g = (Δ.P l).T.hom := by
  have hsh : Presieve.IsSheaf (BigFppfOver.topology B S hS) D.Y.obj :=
    (isSheaf_iff_isSheaf_of_type _ _).1 D.Y.property.isSheaf
  have hfor : Presieve.IsSheafFor D.Y.obj
      (Presieve.ofArrows (fun l => (Δ.P l).T.left) Δ.fP) := by
    rw [Presieve.isSheafFor_iff_generate]
    exact hsh _ hcov
  rw [Presieve.isSheafFor_arrows_iff] at hfor
  have key : ∀ (l : L) {Z : BigFppfOver B S hS} (a : Z ⟶ (Δ.P l).T.left),
      D.Y.obj.map a.op (yonedaEquiv (Δ.P l).T.hom.hom) =
        yonedaEquiv ((schemeSpaceFunctor B S hS).map a ≫ (Δ.P l).T.hom).hom :=
    fun l Z a => yonedaEquiv_naturality _ a
  obtain ⟨t, ht, -⟩ := hfor (fun l => yonedaEquiv (Δ.P l).T.hom.hom) (by
    intro l m Z a a' h
    dsimp only
    rw [key l a, key m a', Δ.compatible_base l m a a' h])
  refine ⟨ObjectProperty.homMk (yonedaEquiv.symm t), fun l => ?_⟩
  refine ObjectProperty.hom_ext _ ?_
  change yoneda.map (Δ.fP l) ≫ yonedaEquiv.symm t = (Δ.P l).T.hom.hom
  rw [yonedaEquiv_symm_naturality_left, ht l]
  exact yonedaEquiv.symm_apply_apply _

variable (g : (schemeSpaceFunctor B S hS).obj U ⟶ D.Y)
  (hg : ∀ l, (schemeSpaceFunctor B S hS).map (Δ.fP l) ≫ g = (Δ.P l).T.hom)

/-- The test scheme `(U, g)` over `Y`. -/
abbrev baseObject : SchemesOver D.Y := CostructuredArrow.mk g

/-- The morphism of test schemes from the test scheme of `P l` to `(U, g)`. -/
def toBase (l : L) : (Δ.P l).T ⟶ baseObject g :=
  CostructuredArrow.homMk (Δ.fP l) (hg l)

/-- The underlying morphism of schemes of `toBase g hg l` is `fP l`. -/
@[simp]
theorem toBase_left (l : L) : (Δ.toBase g hg l).left = Δ.fP l := rfl

/-- The morphism `X_{P l} ⟶ X_U` of base changes. -/
abbrev memberMap (l : L) : D.space (Δ.P l).T ⟶ D.space (baseObject g) :=
  D.relativeMap (Δ.toBase g hg l)

/-- The two composites from the object over a pairwise fibre product to `(U, g)` agree. -/
theorem c_comp_toBase (l m : L) :
    (Δ.c l m).base ≫ Δ.toBase g hg l = (Δ.e l m).base ≫ Δ.toBase g hg m :=
  CostructuredArrow.hom_ext _ _ (Δ.sq₂ l m).w

/-- The base change of an object over a pairwise fibre product is the fibre product of the base
changes. -/
theorem isPullback_pair (l m : L) :
    IsPullback (D.relativeMap (Δ.c l m).base) (D.relativeMap (Δ.e l m).base)
      (Δ.memberMap g hg l) (Δ.memberMap g hg m) :=
  isPullback_baseChangeMap_of_isPullback D.f (Δ.sq₂ l m)

/-- The base change of an object over a triple fibre product is the fibre product of two of the
pairwise ones. -/
theorem isPullback_triple (l m n : L) :
    IsPullback (D.relativeMap (Δ.b₁₂ l m n).base) (D.relativeMap (Δ.b₂₃ l m n).base)
      (D.relativeMap (Δ.e l m).base) (D.relativeMap (Δ.c m n).base) :=
  isPullback_baseChangeMap_of_isPullback D.f (Δ.sq₃ l m n)

/-- The members of the module family. -/
abbrev member (l : L) : AlgebraicSpaces B S hS := D.space (Δ.P l).T

/-- **The identification of the pairwise fibre product of the base changes with the base change
of the object over the pairwise fibre product.** -/
def pairLift (l m : L) : pair B S hS Δ.member (Δ.memberMap g hg) l m ⟶ D.space (Δ.Q l m).T :=
  (Δ.isPullback_pair g hg l m).lift (pairFst B S hS Δ.member (Δ.memberMap g hg) l m)
    (pairSnd B S hS Δ.member (Δ.memberMap g hg) l m)
    (pair_condition B S hS Δ.member (Δ.memberMap g hg) l m)

/-- `pairLift g hg l m` followed by the base change of `c l m` is the first projection. -/
@[reassoc (attr := simp)]
theorem pairLift_fst (l m : L) :
    Δ.pairLift g hg l m ≫ D.relativeMap (Δ.c l m).base =
      pairFst B S hS Δ.member (Δ.memberMap g hg) l m :=
  (Δ.isPullback_pair g hg l m).lift_fst _ _ _

/-- `pairLift g hg l m` followed by the base change of `e l m` is the second projection. -/
@[reassoc (attr := simp)]
theorem pairLift_snd (l m : L) :
    Δ.pairLift g hg l m ≫ D.relativeMap (Δ.e l m).base =
      pairSnd B S hS Δ.member (Δ.memberMap g hg) l m :=
  (Δ.isPullback_pair g hg l m).lift_snd _ _ _

/-- The pairwise isomorphism of the module descent datum. -/
def transition (l m : L) :
    (modulePullback B S hS (pairFst B S hS Δ.member (Δ.memberMap g hg) l m)).obj (Δ.P l).F ≅
      (modulePullback B S hS (pairSnd B S hS Δ.member (Δ.memberMap g hg) l m)).obj (Δ.P m).F :=
  CoherentHom.spanIso (Δ.c l m) (Δ.e l m) (Δ.pairLift g hg l m) _ _
    (Δ.pairLift_fst g hg l m) (Δ.pairLift_snd g hg l m)

/-- The pairwise isomorphism read on a test space is the span isomorphism along the composite
with the identification of the pairwise fibre product. -/
theorem transitionOn_eq {W : AlgebraicSpaces B S hS} (l m : L)
    (v : W ⟶ pair B S hS Δ.member (Δ.memberMap g hg) l m) (vl : W ⟶ Δ.member l)
    (vm : W ⟶ Δ.member m) (hl : v ≫ pairFst B S hS Δ.member (Δ.memberMap g hg) l m = vl)
    (hm : v ≫ pairSnd B S hS Δ.member (Δ.memberMap g hg) l m = vm) :
    transitionOn B S hS Δ.member (Δ.memberMap g hg) (fun l => (Δ.P l).F) (Δ.transition g hg)
        l m v vl vm hl hm =
      CoherentHom.spanIso (Δ.c l m) (Δ.e l m) (v ≫ Δ.pairLift g hg l m) vl vm
        (by rw [Category.assoc, pairLift_fst, hl]) (by rw [Category.assoc, pairLift_snd, hm]) :=
  CoherentHom.spanIso_pullback (Δ.c l m) (Δ.e l m) (Δ.pairLift g hg l m) _ _
    (Δ.pairLift_fst g hg l m) (Δ.pairLift_snd g hg l m) v vl vm hl hm

/-- The pairwise isomorphism read through the object over a triple fibre product. -/
theorem spanIso_eq_comp {l m : L} {A₀ : CoherentObject D} {W : AlgebraicSpaces B S hS}
    (b : CoherentHom A₀ (Δ.Q l m)) (τ : W ⟶ D.space A₀.T)
    (r : W ⟶ D.space (Δ.Q l m).T) (hr : τ ≫ D.relativeMap b.base = r)
    (vl : W ⟶ Δ.member l) (vm : W ⟶ Δ.member m)
    (h₁ : r ≫ D.relativeMap (Δ.c l m).base = vl) (h₂ : r ≫ D.relativeMap (Δ.e l m).base = vm) :
    CoherentHom.spanIso (Δ.c l m) (Δ.e l m) r vl vm h₁ h₂ =
      CoherentHom.spanIso (b.comp (Δ.c l m)) (b.comp (Δ.e l m)) τ vl vm
        (by rw [← h₁, ← hr, Category.assoc, ← CoherentSituation.relativeMap_comp]; rfl)
        (by rw [← h₂, ← hr, Category.assoc, ← CoherentSituation.relativeMap_comp]; rfl) := by
  rw [CoherentHom.spanIso_comp b (Δ.c l m) (Δ.e l m) τ vl vm _ _
    (by rw [hr, h₁]) (by rw [hr, h₂])]
  exact CoherentHom.spanIso_congr _ _ rfl rfl hr.symm _ _

/-- The base change of an object over a triple fibre product, mapped to the outer pairwise one. -/
theorem triple_lift_outer {W : AlgebraicSpaces B S hS} (l m n : L)
    (τ : W ⟶ D.space (Δ.T l m n).T) (vl : W ⟶ Δ.member l) (vn : W ⟶ Δ.member n)
    (vik : W ⟶ pair B S hS Δ.member (Δ.memberMap g hg) l n)
    (hik₀ : vik ≫ pairFst B S hS Δ.member (Δ.memberMap g hg) l n = vl)
    (hik₁ : vik ≫ pairSnd B S hS Δ.member (Δ.memberMap g hg) l n = vn)
    (h₁ : τ ≫ D.relativeMap ((Δ.b₁₂ l m n).comp (Δ.c l m)).base = vl)
    (h₃ : τ ≫ D.relativeMap ((Δ.b₂₃ l m n).comp (Δ.e m n)).base = vn) :
    τ ≫ D.relativeMap (Δ.b₁₃ l m n).base = vik ≫ Δ.pairLift g hg l n := by
  refine (Δ.isPullback_pair g hg l n).hom_ext ?_ ?_
  · rw [Category.assoc, ← CoherentSituation.relativeMap_comp, Category.assoc, pairLift_fst,
      hik₀, ← h₁]
    exact congrArg (fun k => τ ≫ D.relativeMap k)
      (congrArg CoherentHom.base (Δ.hc₁ l m n)).symm
  · rw [Category.assoc, ← CoherentSituation.relativeMap_comp, Category.assoc, pairLift_snd,
      hik₁, ← h₃]
    exact congrArg (fun k => τ ≫ D.relativeMap k)
      (congrArg CoherentHom.base (Δ.hc₃ l m n)).symm

/-- **The cocycle condition of the module descent datum.** -/
theorem transition_cocycle (l m n : L) (W : AlgebraicSpaces B S hS)
    (vi : W ⟶ Δ.member l) (vj : W ⟶ Δ.member m) (vk : W ⟶ Δ.member n)
    (vij : W ⟶ pair B S hS Δ.member (Δ.memberMap g hg) l m)
    (vjk : W ⟶ pair B S hS Δ.member (Δ.memberMap g hg) m n)
    (vik : W ⟶ pair B S hS Δ.member (Δ.memberMap g hg) l n)
    (hij₀ : vij ≫ pairFst B S hS Δ.member (Δ.memberMap g hg) l m = vi)
    (hij₁ : vij ≫ pairSnd B S hS Δ.member (Δ.memberMap g hg) l m = vj)
    (hjk₀ : vjk ≫ pairFst B S hS Δ.member (Δ.memberMap g hg) m n = vj)
    (hjk₁ : vjk ≫ pairSnd B S hS Δ.member (Δ.memberMap g hg) m n = vk)
    (hik₀ : vik ≫ pairFst B S hS Δ.member (Δ.memberMap g hg) l n = vi)
    (hik₁ : vik ≫ pairSnd B S hS Δ.member (Δ.memberMap g hg) l n = vk) :
    transitionOn B S hS Δ.member (Δ.memberMap g hg) (fun l => (Δ.P l).F) (Δ.transition g hg)
        l m vij vi vj hij₀ hij₁ ≪≫
      transitionOn B S hS Δ.member (Δ.memberMap g hg) (fun l => (Δ.P l).F) (Δ.transition g hg)
        m n vjk vj vk hjk₀ hjk₁ =
      transitionOn B S hS Δ.member (Δ.memberMap g hg) (fun l => (Δ.P l).F) (Δ.transition g hg)
        l n vik vi vk hik₀ hik₁ := by
  have hlift : (vij ≫ Δ.pairLift g hg l m) ≫ D.relativeMap (Δ.e l m).base =
      (vjk ≫ Δ.pairLift g hg m n) ≫ D.relativeMap (Δ.c m n).base := by
    rw [Category.assoc, Category.assoc, pairLift_snd, pairLift_fst, hij₁, hjk₀]
  let τ := (Δ.isPullback_triple l m n).lift _ _ hlift
  have τ₁₂ : τ ≫ D.relativeMap (Δ.b₁₂ l m n).base = vij ≫ Δ.pairLift g hg l m :=
    (Δ.isPullback_triple l m n).lift_fst _ _ _
  have τ₂₃ : τ ≫ D.relativeMap (Δ.b₂₃ l m n).base = vjk ≫ Δ.pairLift g hg m n :=
    (Δ.isPullback_triple l m n).lift_snd _ _ _
  have h₁ : τ ≫ D.relativeMap ((Δ.b₁₂ l m n).comp (Δ.c l m)).base = vi := by
    change τ ≫ D.relativeMap ((Δ.b₁₂ l m n).base ≫ (Δ.c l m).base) = vi
    rw [CoherentSituation.relativeMap_comp, ← Category.assoc, τ₁₂, Category.assoc, pairLift_fst,
      hij₀]
  have h₃ : τ ≫ D.relativeMap ((Δ.b₂₃ l m n).comp (Δ.e m n)).base = vk := by
    change τ ≫ D.relativeMap ((Δ.b₂₃ l m n).base ≫ (Δ.e m n).base) = vk
    rw [CoherentSituation.relativeMap_comp, ← Category.assoc, τ₂₃, Category.assoc, pairLift_snd,
      hjk₁]
  have τ₁₃ := Δ.triple_lift_outer g hg l m n τ vi vk vik hik₀ hik₁ h₁ h₃
  rw [Δ.transitionOn_eq, Δ.transitionOn_eq, Δ.transitionOn_eq,
    Δ.spanIso_eq_comp (Δ.b₁₂ l m n) τ _ τ₁₂, Δ.spanIso_eq_comp (Δ.b₂₃ l m n) τ _ τ₂₃,
    Δ.spanIso_eq_comp (Δ.b₁₃ l m n) τ _ τ₁₃]
  rw [CoherentHom.spanIso_congr vj vk (Δ.hc₂ l m n).symm rfl rfl _ _,
    CoherentHom.spanIso_trans,
    CoherentHom.spanIso_congr vi vk (Δ.hc₁ l m n) (Δ.hc₃ l m n) rfl _ _]

/-- **The descent datum of quasi-coherent modules of a descent diagram** (Stacks 04W3), relative
to the family of morphisms of base changes `X_{P l} ⟶ X_U`. -/
def moduleDatum : DescentDatum B S hS Δ.member (Δ.memberMap g hg) where
  F l := (Δ.P l).F
  quasicoherent l := (Δ.P l).quasicoherent
  transition := Δ.transition g hg
  cocycle l m n W vi vj vk vij vjk vik hij₀ hij₁ hjk₀ hjk₁ hik₀ hik₁ :=
    Δ.transition_cocycle g hg l m n W vi vj vk vij vjk vik hij₀ hij₁ hjk₀ hjk₁ hik₀ hik₁

end CoherentDescentDiagram

end AlgebraicGeometry.Space

end
