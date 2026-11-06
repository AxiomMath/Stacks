module

public import StacksFrontier.AlgebraicGeometry.Stacks.TensorPushforwardPlanes
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentHigherDirectImageDeltaFunctor
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.CoheratorMonoidal
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.CoheratorCanonical
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfTensorAffineSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineFlatBaseChangeSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfModulesBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeTensor
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStackTerminalSubsite
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedUniquePointStack
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactQuasiSeparatedStack
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedSchemeStack
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactStructureMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Representable
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductSquareAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactPointRepresentative
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.ContainingSet

/-!
# Stacks 0GRN fails as printed: the counterexample on algebraic stacks

**Stacks 0GRN** asserts that for 1-morphisms `a : 𝒴 ⟶ 𝒳`, `b : 𝒵 ⟶ 𝒳` of algebraic stacks which
are representable by schemes, quasi-compact, quasi-separated and flat,

`a_{QCoh,*}𝒪_𝒴 ⊗_{𝒪_𝒳} b_{QCoh,*}𝒪_𝒵 = f_{QCoh,*}𝒪_{𝒴 ×_𝒳 𝒵}`

for the projection `f` of the 2-fibre product. This file proves that this is false, with
`QCoh(𝒪_𝒳)` the quasi-coherent modules
`AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentModules` with the monoidal structure of
**Stacks 0GQM** (`AlgebraicGeometry.Stack.AlgebraicStacks.fppfModulesMonoidal` restricted to the
full subcategory) and `f_{QCoh,*}` the quasi-coherent direct image
`AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentDirectImage` of **Stacks 077A**.

The counterexample is the scheme-level one of `AlgebraicGeometry.TensorPushforwardPlanes`, read
on the algebraic stacks of schemes: `X = Spec A`, `A = k[x, y, z, w] / (xz, xw, yz, yw)` (two
planes meeting at the origin), over itself, and `a`, `b` the open immersions of the punctured
planes `V = D(z) ∪ D(w)` and `W = D(x) ∪ D(y)`.

* **The right hand side is zero.** For any 2-commutative square over `(a, b)`, an object of the
  apex lies over a scheme `T` with maps to `V` and to `W` agreeing in `X` up to an automorphism of
  `T`; as `V ∩ W = ∅`, `T` is empty, so every module on the apex is zero and so is its direct image
  (`AlgebraicGeometry.Stack.AlgebraicStacks.TensorPushforwardPlanes.isEmpty_of_twoCommSq`,
  `AlgebraicGeometry.Stack.AlgebraicStacks.isZero_pushforwardUnit_of_isEmpty`).
* **The left hand side is not.** The sections over `id_X` of `a_{QCoh,*}𝒪_V = Q(a_*𝒪_V)` are those
  of `a_*𝒪_V` (`id_X` is a flat object; **Stacks 0GQQ**), which are `Γ(V, 𝒪)` semilinearly over the
  restriction `Γ(X, 𝒪) → Γ(V, 𝒪)` (the sections formula of a direct image at a terminal arrow,
  which is semilinear: `fppfModulesPushforwardSectionsIsoOfIsTerminal_hom_smul`). The sections over
  `id_X` of the tensor product are the tensor product of the sections (the factors being in
  `LQCoh^fbc`; `AlgebraicGeometry.FibredSite.bijective_sheafTensor_unit_app_of_isAffine`), and the
  two evaluations at the origin `Γ(V, 𝒪) → k`, `Γ(W, 𝒪) → k`, which agree on `Γ(X, 𝒪)`, give a
  nonzero balanced map on it.

The failing step of the source's proof is its last: the Künneth formula (**Lemma 0FLQ**) gives
`Rf_*𝒪 = Ra_*𝒪 ⊗^𝐋 Rb_*𝒪`, and `H⁰` of the right hand side is `a_*𝒪 ⊗ b_*𝒪` only when the higher
cohomology or the flatness permits; here `H¹(V, 𝒪) ≠ 0` and `Γ(V, 𝒪) = k[z, w] = A / (x, y)` is not
flat over `A`.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.not_forall_nonempty_tensorPushforwardUnits_iso`:
  **Stacks 0GRN as printed is false**.
* `AlgebraicGeometry.Stack.AlgebraicStacks.TensorPushforwardPlanes.counterexample`: the
  counterexample with its four hypotheses on each leg.
* `AlgebraicGeometry.Stack.AlgebraicStacks.TensorPushforwardPlanes.isEmpty_tensorIso`: for every
  2-commutative square over the two punctured planes there is no isomorphism.

General results used on the way:

* `AlgebraicGeometry.BigFppfOver.isRepresentableMorphism_of_forall_isRepresentable` and
  `AlgebraicGeometry.Stack.AlgebraicStacks.isRepresentableMorphism_schemeStackMap`: a morphism of
  the site gives a 1-morphism representable by schemes.
* `AlgebraicGeometry.Stack.AlgebraicStacks.fppfModulesPushforwardSectionsIsoOfIsTerminal_hom_smul`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.exists_eval_pushforwardUnit` and
  `AlgebraicGeometry.Stack.AlgebraicStacks.not_isZero_tensorObj_of_eval`.

## Implementation notes

The generic lemmas are stated for arbitrary algebraic stacks and only then specialised: on the
concrete stacks of schemes, the kernel's check that the additive structure of a module of sections
agrees with that of the underlying ring unfolds the structure sheaf of the spectrum, while for a
variable stack it is immediate.

## References

* [Stacks Project, Tag 0GRN](https://stacks.math.columbia.edu/tag/0GRN)
* [Stacks Project, Tag 0GQQ](https://stacks.math.columbia.edu/tag/0GQQ)
* [Stacks Project, Tag 0GQM](https://stacks.math.columbia.edu/tag/0GQM)
* [Stacks Project, Tag 077A](https://stacks.math.columbia.edu/tag/077A)
* [Stacks Project, Tag 0FLQ](https://stacks.math.columbia.edu/tag/0FLQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

attribute [local instance] hasSheafCompose_forget_ringCat
  hasSheafCompose_forget_commRingCat Stacks.hasSheafCompose_forget₂_commRingCat
  FlatFppf.hasSheafify_addCommGrpCat FlatFppf.wEqualsLocallyBijective_addCommGrpCat
  FlatFppf.hasSheafify_fppf_addCommGrpCat FlatFppf.wEqualsLocallyBijective_fppf_addCommGrpCat
  FlatFppf.hasSheafify_associatedTopology_ab
  FlatFppf.wEqualsLocallyBijective_fppfTopology_addCommGrpCat
  fppfModulesMonoidal fppfModulesBraided fppfModulesSymmetric

/-! ### Generic facts -/

/-- The addition of the unit module is the addition of the ring. -/
lemma _root_.Stacks.SheafOfModules.unit_add {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {X : Cᵒᵖ} (a b : (SheafOfModules.unit R).val.obj X) :
    @id (R.obj.obj X) (a + b) = @id (R.obj.obj X) a + @id (R.obj.obj X) b :=
  rfl

/-- The scalar multiplication of the unit module is the multiplication of the ring. -/
lemma _root_.Stacks.SheafOfModules.unit_smul {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}} {X : Cᵒᵖ} (s : R.obj.obj X)
    (a : (SheafOfModules.unit R).val.obj X) :
    @id (R.obj.obj X) (s • a) = s * @id (R.obj.obj X) a :=
  rfl

/-- A morphism between the abelian groups of sections of two sheaves of modules is additive for
the additions of the modules. -/
lemma _root_.Stacks.SheafOfModules.toAbelianPresheaf_map_add {C C' : Type*} [Category C]
    [Category C'] {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}
    {R : Sheaf J RingCat.{u}} {R' : Sheaf J' RingCat.{u}} {P : SheafOfModules.{u} R}
    {Q : SheafOfModules.{u} R'} {X : Cᵒᵖ} {X' : C'ᵒᵖ}
    (g : (Stacks.SheafOfModules.toAbelianPresheaf R ⋙ (evaluation Cᵒᵖ AddCommGrpCat).obj X).obj P ⟶
      (Stacks.SheafOfModules.toAbelianPresheaf R' ⋙
        (evaluation C'ᵒᵖ AddCommGrpCat).obj X').obj Q)
    (a b : P.val.obj X) :
    @id (Q.val.obj X') (g (a + b)) =
      @id (Q.val.obj X') (g a) + @id (Q.val.obj X') (g b) :=
  g.hom.map_add a b

section Generic

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The structure sheaf `𝒪_𝒴`, the unit of `QCoh(𝒪_𝒴)`. -/
abbrev qcUnit (𝒴 : AlgebraicStacks.{u, w} B S hS) : quasicoherentModules B S hS 𝒴 := 𝟙_ _

/-- `f_{QCoh,*}𝒪`, for a 1-morphism `f : 𝒴 ⟶ 𝒳` of algebraic stacks. -/
abbrev pushforwardUnit {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒴 ⟶ 𝒳) :
    quasicoherentModules B S hS 𝒳 :=
  (quasicoherentDirectImage B S hS f).obj (qcUnit 𝒴)

/-- The left hand side `a_{QCoh,*}𝒪_𝒴 ⊗_{𝒪_𝒳} b_{QCoh,*}𝒪_𝒵` of Stacks 0GRN. -/
abbrev tensorPushforwardUnits {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS} (a : 𝒴 ⟶ 𝒳)
    (b : 𝒵 ⟶ 𝒳) : quasicoherentModules B S hS 𝒳 :=
  pushforwardUnit a ⊗ pushforwardUnit b

/-- The 1-morphism of algebraic stacks of a morphism of the site is representable (by
schemes). -/
theorem isRepresentableMorphism_schemeStackMap {U V : BigFppfOver B S hS} (g : U ⟶ V) :
    Stacks.RepresentableMorphism.IsRepresentableMorphism
      (schemeStack.{u, w} B S hS U).val.val.p (schemeStack.{u, w} B S hS V).val.val.p
      (CatFiberedInGroupoids.homFunctor (schemeStackMap.{u, w} B S hS g).hom) := by
  have := AlgebraicGeometry.hasPullbacks_bigFppfOver B S hS
  refine BigFppfOver.isRepresentableMorphism_of_forall_isRepresentable (Over.map g) rfl
    (Functor.IsFiberedInGroupoids.over_forget U) (Functor.IsFiberedInGroupoids.over_forget V)
    (fun y => ⟨(Over.pullback g).obj y, ⟨?_⟩⟩)
  exact
    { homEquiv := ((Over.mapPullbackAdj g).homEquiv _ y).symm
      homEquiv_comp := fun f h => (Over.mapPullbackAdj g).homEquiv_naturality_left_symm f h }

/-- The ring map `𝒪_𝒴(y) ⟶ 𝒪_𝒳(x₀)` that the structure map of the direct image along `f` cuts out
at an arrow `t : f(x₀) ⟶ y`: the leg of the right Kan extension of the structure sheaf. -/
def pushforwardSectionsRingHom {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    {y : 𝒴.val.val.obj} (t : CostructuredArrow (CatFiberedInGroupoids.homFunctor f.hom) y) :
    (FibredSite.ringStructureSheafCore B S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids
      .fppf).obj.obj (op y) →+*
    (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
      .fppf).obj.obj (op t.left) :=
  (Stacks.SheafOfModules.scalarπ (CatFiberedInGroupoids.homFunctor f.hom)
    (moduleDirectImageStructureMap B S hS 𝒳.val.val.p 𝒴.val.val.p 𝒳.val.isFiberedInGroupoids
      𝒴.val.isFiberedInGroupoids (CatFiberedInGroupoids.homFunctor f.hom)
      (CatFiberedInGroupoids.homFunctor_comp_p f.hom) B.topology le_rfl).hom (op y)
      (StructuredArrow.mk (Y := op t.left) t.hom.op)).hom

/-- **The sections formula for the fppf direct image is semilinear.** For a terminal arrow
`t : f(x₀) ⟶ y` the identification `Γ(y, f_* M) ≅ Γ(x₀, M)` of
`AlgebraicGeometry.Stack.fppfModulesPushforwardSectionsIsoOfIsTerminal` carries multiplication by
`r ∈ 𝒪_𝒴(y)` to multiplication by its image under `pushforwardSectionsRingHom`. -/
theorem fppfModulesPushforwardSectionsIsoOfIsTerminal_hom_smul
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) {y : 𝒴.val.val.obj}
    {t : CostructuredArrow (CatFiberedInGroupoids.homFunctor f.hom) y} (ht : IsTerminal t)
    (M : Stack.fppfModules B S hS 𝒳)
    (r : (FibredSite.ringStructureSheafCore B S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids
      .fppf).obj.obj (op y))
    (m : ((fppfModulesPushforward B S hS f).obj M).val.obj (op y)) :
    @id (M.val.obj (op t.left))
        (((fppfModulesPushforwardSectionsIsoOfIsTerminal B S hS f ht).hom.app M).hom (r • m)) =
      pushforwardSectionsRingHom f t r • @id (M.val.obj (op t.left))
        (((fppfModulesPushforwardSectionsIsoOfIsTerminal B S hS f ht).hom.app M).hom m) := by
  let ι := ((fppfModulesPushforwardIsoModuleDirectImage B S hS f).hom.app M).val.app (op y)
  have h1 : ι (r • m) = r • ι m := ι.hom.map_smul r m
  have key := Stacks.SheafOfModules.ranSMul_π (CatFiberedInGroupoids.homFunctor f.hom)
    (moduleDirectImageStructureMap B S hS 𝒳.val.val.p 𝒴.val.val.p 𝒳.val.isFiberedInGroupoids
      𝒴.val.isFiberedInGroupoids (CatFiberedInGroupoids.homFunctor f.hom)
      (CatFiberedInGroupoids.homFunctor_comp_p f.hom) B.topology le_rfl).hom M.val (op y) r
    (StructuredArrow.mk (Y := op t.left) t.hom.op)
  change (Stacks.SheafOfModules.ranπ (CatFiberedInGroupoids.homFunctor f.hom).op M.val.presheaf
      (op y) (StructuredArrow.mk (Y := op t.left) t.hom.op)) (ι (r • m)) = _
  rw [h1]
  exact ConcreteCategory.congr_hom key (ι m)

/-- On an algebraic stack all of whose objects lie over the empty scheme, every module is
zero. -/
theorem isZero_fppfModules_of_isEmpty (𝒲 : AlgebraicStacks.{u, w} B S hS)
    (h : ∀ x : 𝒲.val.val.obj, IsEmpty ((BigFppfOver.toScheme B S hS).obj (𝒲.val.val.p.obj x)))
    (M : Stack.fppfModules B S hS 𝒲) : IsZero M := by
  rw [isZero_sheafOfModules_iff_forall_subsingleton]
  intro X
  have := h X.unop
  have : Subsingleton ((FibredSite.ringStructureSheafCore B S hS 𝒲.val.val.p
      𝒲.val.isFiberedInGroupoids .fppf).obj.obj X) :=
    inferInstanceAs (Subsingleton Γ((BigFppfOver.toScheme B S hS).obj (𝒲.val.val.p.obj X.unop),
      ⊤))
  exact Module.subsingleton ((FibredSite.ringStructureSheafCore B S hS 𝒲.val.val.p
      𝒲.val.isFiberedInGroupoids .fppf).obj.obj X) _

/-- If every object of `𝒲` lies over the empty scheme, then `f_{QCoh,*}𝒪_𝒲 = 0`. -/
theorem isZero_pushforwardUnit_of_isEmpty {𝒳 𝒲 : AlgebraicStacks.{u, w} B S hS} (f : 𝒲 ⟶ 𝒳)
    (h : ∀ x : 𝒲.val.val.obj, IsEmpty ((BigFppfOver.toScheme B S hS).obj (𝒲.val.val.p.obj x))) :
    IsZero (pushforwardUnit f) := by
  have h1 := (fppfModulesPushforward B S hS f).map_isZero
    (isZero_fppfModules_of_isEmpty 𝒲 h ((quasicoherentInclusion B S hS 𝒲).obj (𝟙_ _)))
  have : (coherator B S hS 𝒳).IsRightAdjoint := (coheratorAdjunction B S hS 𝒳).isRightAdjoint
  exact (coherator B S hS 𝒳).map_isZero h1

/-- `f_{QCoh,*}𝒪 = Q(f_*𝒪)`, on the nose. -/
lemma pushforwardUnit_eq {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒴 ⟶ 𝒳) :
    pushforwardUnit f = (coherator B S hS 𝒳).obj
      ((fppfModulesPushforward B S hS f).obj ((quasicoherentInclusion B S hS 𝒴).obj (qcUnit 𝒴))) :=
  rfl

/-- **A character of the functions at the terminal arrow gives a semilinear functional on the
sections of `f_{QCoh,*}𝒪` over a flat object.** Let `f : 𝒴 ⟶ 𝒳` be quasi-compact and
quasi-separated, `x₀` a flat object of `𝒳`, `t : f(y₀) ⟶ x₀` terminal and `ε` a ring map out of
`𝒪_𝒴(y₀)`. Then the sections over `x₀` of `f_{QCoh,*}𝒪_𝒴` carry an additive functional,
semilinear over `ε ∘ pushforwardSectionsRingHom f t`, taking the value `1`. -/
theorem exists_eval_pushforwardUnit {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒴 ⟶ 𝒳)
    (hqc : IsQuasiCompactMorphism B S hS f) (hqs : AlgebraicStacks.IsQuasiSeparated B S hS f)
    {x₀ : 𝒳.val.val.obj} (hx₀ : flatObject B S hS 𝒳.val x₀)
    {t : CostructuredArrow (CatFiberedInGroupoids.homFunctor f.hom) x₀} (ht : IsTerminal t)
    {K : Type*} [CommRing K]
    (ε : (FibredSite.ringStructureSheafCore B S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids
      .fppf).obj.obj (op t.left) →+* K) :
    ∃ (l : (pushforwardUnit f).obj.val.obj (op x₀) → K)
      (m₀ : (pushforwardUnit f).obj.val.obj (op x₀)),
      l m₀ = 1 ∧ (∀ m m', l (m + m') = l m + l m') ∧
        ∀ (r : (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
            .fppf).obj.obj (op x₀)) m,
          l (r • m) = ε (pushforwardSectionsRingHom f t r) * l m := by
  have hc := (bijective_coheratorAdjunction_counit_directImage B S hS f hqc hqs (qcUnit _) x₀
    hx₀).1
  let N := (fppfModulesPushforward B S hS f).obj ((quasicoherentInclusion B S hS 𝒴).obj (qcUnit 𝒴))
  let c : (pushforwardUnit f).obj.val.obj (op x₀) ⟶ N.val.obj (op x₀) :=
    ((coheratorAdjunction B S hS 𝒳).counit.app N).val.app (op x₀)
  let R := FibredSite.ringStructureSheafCore B S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids .fppf
  let e : (Stacks.SheafOfModules.toAbelianPresheaf _ ⋙ (evaluation _ AddCommGrpCat).obj
        (op x₀)).obj N ≅
      (Stacks.SheafOfModules.toAbelianPresheaf R ⋙ (evaluation _ AddCommGrpCat).obj
        (op t.left)).obj (SheafOfModules.unit R) :=
    ((fppfModulesPushforwardSectionsIsoOfIsTerminal B S hS f ht).app
      ((quasicoherentInclusion B S hS 𝒴).obj (qcUnit 𝒴)))
  have he : Function.Bijective e.hom := ConcreteCategory.bijective_of_isIso e.hom
  let l := fun m => ε (@id (R.obj.obj (op t.left)) (e.hom (c m)))
  obtain ⟨n₀, hn₀⟩ := he.2 (1 : R.obj.obj (op t.left))
  obtain ⟨m₀, hm₀⟩ := hc.2 n₀
  refine ⟨l, m₀, ?_, fun m m' => ?_, fun r m => ?_⟩
  · change ε (@id (R.obj.obj (op t.left)) (e.hom (c m₀))) = 1
    rw [show c m₀ = n₀ from hm₀, hn₀]
    exact map_one ε
  · change ε (@id (R.obj.obj (op t.left)) (e.hom (c (m + m')))) =
      ε (@id (R.obj.obj (op t.left)) (e.hom (c m))) + ε (@id (R.obj.obj (op t.left)) (e.hom (c m')))
    have h3 : @id (R.obj.obj (op t.left)) (e.hom (c m + c m')) =
        @id (R.obj.obj (op t.left)) (e.hom (c m)) + @id (R.obj.obj (op t.left)) (e.hom (c m')) :=
      (Stacks.SheafOfModules.toAbelianPresheaf_map_add e.hom (c m) (c m')).trans
        (Stacks.SheafOfModules.unit_add _ _)
    rw [map_add, h3, map_add]
  · change ε (@id (R.obj.obj (op t.left)) (e.hom (c (r • m)))) =
      ε (pushforwardSectionsRingHom f t r) * ε (@id (R.obj.obj (op t.left)) (e.hom (c m)))
    have h1 : c (r • m) = r • c m := c.hom.map_smul r m
    have h4 : @id (R.obj.obj (op t.left)) (e.hom (r • c m)) =
        pushforwardSectionsRingHom f t r * @id (R.obj.obj (op t.left)) (e.hom (c m)) :=
      (fppfModulesPushforwardSectionsIsoOfIsTerminal_hom_smul f ht
        ((quasicoherentInclusion B S hS 𝒴).obj (qcUnit 𝒴)) r (c m)).trans
        (Stacks.SheafOfModules.unit_smul _ _)
    rw [h1, h4, map_mul]

/-- A tensor product of modules is nontrivial as soon as its factors carry additive functionals,
semilinear over a common character into a nontrivial ring and taking the value `1`. -/
lemma _root_.PresheafOfModules.nontrivial_tensorObj_obj_of_eval {C : Type*} [Category C]
    {O : Cᵒᵖ ⥤ CommRingCat.{u}} (M₁ M₂ : PresheafOfModules.{u} (O ⋙ forget₂ _ _)) (X : Cᵒᵖ)
    {K : Type*} [CommRing K] [Nontrivial K] (χ : O.obj X →+* K) (l₁ : M₁.obj X → K)
    (l₂ : M₂.obj X → K) (hadd₁ : ∀ m m', l₁ (m + m') = l₁ m + l₁ m')
    (hadd₂ : ∀ m m', l₂ (m + m') = l₂ m + l₂ m')
    (hsmul₁ : ∀ (r : O.obj X) m, l₁ (r • m) = χ r * l₁ m)
    (hsmul₂ : ∀ (r : O.obj X) m, l₂ (r • m) = χ r * l₂ m)
    (m₁ : M₁.obj X) (m₂ : M₂.obj X) (h₁ : l₁ m₁ = 1) (h₂ : l₂ m₂ = 1) :
    Nontrivial ((PresheafOfModulesOfCommRing.Monoidal.tensorObj M₁ M₂).obj X) := by
  let : Algebra (O.obj X) K := χ.toAlgebra
  let L₁ : M₁.obj X →ₗ[O.obj X] K :=
    { toFun := l₁
      map_add' := hadd₁
      map_smul' := fun r m => by rw [hsmul₁, RingHom.id_apply, Algebra.smul_def]; rfl }
  let L₂ : M₂.obj X →ₗ[O.obj X] K :=
    { toFun := l₂
      map_add' := hadd₂
      map_smul' := fun r m => by rw [hsmul₂, RingHom.id_apply, Algebra.smul_def]; rfl }
  let Φ : TensorProduct (O.obj X) (M₁.obj X) (M₂.obj X) →ₗ[O.obj X] K :=
    TensorProduct.lift ((LinearMap.mul (O.obj X) K).compl₁₂ L₁ L₂)
  have hΦ : Φ (m₁ ⊗ₜ m₂) = 1 := by
    simp only [Φ, TensorProduct.lift.tmul, LinearMap.compl₁₂_apply, LinearMap.mul_apply']
    change l₁ m₁ * l₂ m₂ = 1
    rw [h₁, h₂, one_mul]
  exact ⟨⟨m₁ ⊗ₜ m₂, 0, fun h => one_ne_zero (hΦ.symm.trans ((congrArg Φ h).trans
    (map_zero Φ)))⟩⟩

/-- **A tensor product of quasi-coherent modules is nonzero as soon as its factors carry
functionals over an affine object, semilinear over a common character and taking the value
`1`.** -/
theorem not_isZero_tensorObj_of_eval {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (F G : quasicoherentModules B S hS 𝒳) {x₀ : 𝒳.val.val.obj}
    (hx₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x₀)))
    {K : Type*} [CommRing K] [Nontrivial K]
    (χ : (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
      .fppf).obj.obj (op x₀) →+* K)
    (lF : F.obj.val.obj (op x₀) → K) (lG : G.obj.val.obj (op x₀) → K)
    (haddF : ∀ m m', lF (m + m') = lF m + lF m') (haddG : ∀ m m', lG (m + m') = lG m + lG m')
    (hsmulF : ∀ r m, lF (r • m) = χ r * lF m) (hsmulG : ∀ r m, lG (r • m) = χ r * lG m)
    (mF : F.obj.val.obj (op x₀)) (mG : G.obj.val.obj (op x₀)) (hF : lF mF = 1)
    (hG : lG mG = 1) : ¬ IsZero (F ⊗ G) := by
  intro hT
  have hT' : IsZero (F ⊗ G).obj := (quasicoherentInclusion B S hS 𝒳).map_isZero hT
  have hsub := (isZero_sheafOfModules_iff_forall_subsingleton _).1 hT' (op x₀)
  let E := associatedBigEtaleSite B
  have h : E.cutoff = B.cutoff := rfl
  have key := fun (H : quasicoherentModules B S hS 𝒳) {z x : 𝒳.val.val.obj} (ψ : z ⟶ x) hz hx hψ =>
    isIso_restrictionBaseChange_of_flat B E h S hS _ _ H.obj.val
      (lqcohSheafFbcFppfModules_quasicoherentInclusion B E h S hS 𝒳 H) ψ hψ hz hx
  have hbij := FibredSite.bijective_sheafTensor_unit_app_of_isAffine B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids F.obj G.obj (key F) (key G) hx₀
  have hnt := PresheafOfModules.nontrivial_tensorObj_obj_of_eval
    (O := (FibredSite.structureSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf).obj)
    F.obj.val G.obj.val (op x₀) χ lF lG haddF haddG hsmulF hsmulG mF mG hF hG
  obtain ⟨a, b, hab⟩ := hnt
  exact hab (hbij.1 (@Subsingleton.elim _ hsub _ _))

end Generic

namespace TensorPushforwardPlanes

open AlgebraicGeometry.TensorPushforwardPlanes

variable (k : Type u) [Field k]

/-- `X = Spec A`. -/
abbrev planesScheme : Scheme.{u} := Spec (CommRingCat.of (planesRing k))

variable (B : BigFppfSite.{u}) (hS : B.Contains (planesScheme k))

/-- `X` as an object of the big fppf site over itself. -/
abbrev baseObj : BigFppfOver B (planesScheme k) hS := Over.mk (𝟙 _)

include hS in
/-- Every open subscheme of `X` lies in the big fppf site `B`. -/
lemma contains_opens (U : (planesScheme k).Opens) : B.Contains U.toScheme :=
  lt_of_le_of_lt (Scheme.size_le_of_isOpenImmersion U.ι) hS

/-- An open of `X` as an object of the big fppf site over `X`. -/
abbrev opensObj (U : (planesScheme k).Opens) : BigFppfOver B (planesScheme k) hS :=
  siteObject B (planesScheme k) hS (contains_opens k B hS U) U.ι

/-- The open immersion of an open of `X`, as a morphism of the big fppf site over `X`. -/
abbrev opensHom (U : (planesScheme k).Opens) : opensObj k B hS U ⟶ baseObj k B hS :=
  Over.homMk (ObjectProperty.homMk U.ι) (by cat_disch)

/-- The open immersion `V → X` as a 1-morphism of algebraic stacks. -/
abbrev opensMap (U : (planesScheme k).Opens) :
    schemeStack.{u, w} B _ hS (opensObj k B hS U) ⟶ schemeStack.{u, w} B _ hS (baseObj k B hS) :=
  schemeStackMap B _ hS (opensHom k B hS U)

/-! ### The right hand side vanishes -/

/-- Over the open immersions of two disjoint opens `U`, `U'` of `X`, every 2-commutative square
has empty apex: every object of the apex lies over the empty scheme. -/
theorem isEmpty_of_twoCommSq {U U' : (planesScheme k).Opens} (hUU' : U ⊓ U' = ⊥)
    (sq : Bicategory.TwoCommSq (opensMap.{u, w} k B hS U) (opensMap.{u, w} k B hS U'))
    (x : sq.pt.val.val.obj) :
    IsEmpty ((BigFppfOver.toScheme B _ hS).obj (sq.pt.val.val.p.obj x)) := by
  let φ := sq.iso.hom.hom.hom.toNatTrans.app x
  have hy := Functor.congr_obj (CatFiberedInGroupoids.homFunctor_comp_p sq.fst.hom) x
  rw [← hy]
  refine ⟨fun t => ?_⟩
  let y := (CatFiberedInGroupoids.homFunctor sq.fst.hom).obj x
  let z := (CatFiberedInGroupoids.homFunctor sq.snd.hom).obj x
  have hw : φ.left ≫ z.hom ≫ opensHom k B hS U' = y.hom ≫ opensHom k B hS U := Over.w φ
  have h1 := congrArg (fun m => ((BigFppfOver.toScheme B _ hS).map m) t) hw
  simp only at h1
  let a : U.toScheme := (BigFppfOver.toScheme B _ hS).map y.hom t
  let b : U'.toScheme := (BigFppfOver.toScheme B _ hS).map z.hom
    ((BigFppfOver.toScheme B _ hS).map φ.left t)
  have hab : U.ι a = U'.ι b := h1.symm
  have hmem : U.ι a ∈ U ⊓ U' := ⟨a.2, hab ▸ b.2⟩
  rw [hUU'] at hmem
  exact hmem

/-! ### Sections of the left hand side over `X` -/

/-- The object `id_X` of the stack of `X`. -/
abbrev baseTop : (schemeStack.{u, w} B _ hS (baseObj k B hS)).val.val.obj := Over.mk (𝟙 _)

/-- The terminal arrow of `CostructuredArrow (U → X) (id_X)`: `id_U` with the open immersion. -/
def opensArrow (U : (planesScheme k).Opens) :
    CostructuredArrow (CatFiberedInGroupoids.homFunctor (opensMap.{u, w} k B hS U).hom)
      (baseTop.{u, w} k B hS) :=
  CostructuredArrow.mk (Y := (Over.mk (𝟙 (opensObj k B hS U)) :
      (schemeStack.{u, w} B _ hS (opensObj k B hS U)).val.val.obj))
    (Over.homMk (opensHom k B hS U) (by cat_disch))

/-- `opensArrow` is terminal. -/
def isTerminalOpensArrow (U : (planesScheme k).Opens) : IsTerminal (opensArrow.{u, w} k B hS U) :=
  IsTerminal.ofUniqueHom
    (fun Z => CostructuredArrow.homMk (Over.homMk Z.left.hom (by cat_disch))
      ((Over.mkIdTerminal (X := baseObj k B hS)).hom_ext _ _))
    (fun Z m => CostructuredArrow.hom_ext _ _
      ((Over.mkIdTerminal (X := opensObj k B hS U)).hom_ext _ _))

/-- The ring map at the terminal arrow is restriction of functions along `U → X`. -/
lemma pushforwardSectionsRingHom_opensArrow (U : (planesScheme k).Opens)
    (r : Γ(planesScheme k, ⊤)) :
    pushforwardSectionsRingHom (opensMap.{u, w} k B hS U) (opensArrow.{u, w} k B hS U) r =
      U.ι.appTop r := by
  rw [pushforwardSectionsRingHom, scalarπ_moduleDirectImageStructureMap]
  rfl

/-! ### The four hypotheses of Stacks 0GRN on an open immersion into `X` -/

/-- An open immersion into `X = Spec A` with quasi-compact source is quasi-compact and
quasi-separated as a 1-morphism of algebraic stacks. -/
theorem isQuasiCompactMorphism_and_isQuasiSeparated_opensMap (U : (planesScheme k).Opens)
    (hU : IsCompact (U : Set (planesScheme k))) :
    IsQuasiCompactMorphism.{u, w} B _ hS (opensMap.{u, w} k B hS U) ∧
      AlgebraicStacks.IsQuasiSeparated.{u, w} B _ hS (opensMap.{u, w} k B hS U) := by
  have hc : CompactSpace ((BigFppfOver.toScheme B _ hS).obj (opensObj k B hS U)) :=
    isCompact_iff_compactSpace.1 hU
  exact isQuasiCompactMorphism_and_isQuasiSeparated B _ hS inferInstance _
    (isQuasiCompactStack_schemeStack_of_compactSpace.{u, w} B _ hS _ hc)
    (isQuasiSeparatedOver_schemeStack.{u, w} B _ hS _ (quasiSeparatedSpace_of_quasiSeparated U.ι))
    (isQuasiSeparatedOver_schemeStack_of_isAffine.{u, w} B _ hS _
      (inferInstanceAs (IsAffine (planesScheme k))))

/-- An open immersion into `X` is flat as a 1-morphism of algebraic stacks. -/
theorem isFlat_opensMap (U : (planesScheme k).Opens) :
    AlgebraicStacks.IsFlat B _ hS (opensMap.{u, w} k B hS U) :=
  isFlat_schemeFibredCategoryMap.{u, w} B _ hS _ (inferInstanceAs (Flat U.ι))

/-- The punctured plane `V = D(z) ∪ D(w)` is quasi-compact. -/
lemma isCompact_openV :
    IsCompact ((openV k : TopologicalSpace.Opens (PrimeSpectrum (planesRing k))) :
      Set (PrimeSpectrum (planesRing k))) :=
  (PrimeSpectrum.isCompact_basicOpen _).union (PrimeSpectrum.isCompact_basicOpen _)

/-- The punctured plane `W = D(x) ∪ D(y)` is quasi-compact. -/
lemma isCompact_openW :
    IsCompact ((openW k : TopologicalSpace.Opens (PrimeSpectrum (planesRing k))) :
      Set (PrimeSpectrum (planesRing k))) :=
  (PrimeSpectrum.isCompact_basicOpen _).union (PrimeSpectrum.isCompact_basicOpen _)

/-- Restricting a global function of `X` to an open `U`, read through `U.topIso`, is the
restriction map of the structure presheaf of `X` along `U ≤ ⊤`. -/
lemma topIso_hom_ι_appTop (U : (planesScheme k).Opens) (r : Γ(planesScheme k, ⊤)) :
    U.topIso.hom (U.ι.appTop r) = (planesScheme k).presheaf.map (homOfLE le_top : U ⟶ ⊤).op r := by
  simp only [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom]
  rfl

/-- The evaluation at the origin of the punctured plane `U`, read on the functions of the stack of
`U` at `id_U`. -/
def evalOpens (U : (planesScheme k).Opens)
    (ε : (Spec.structureSheaf (planesRing k)).obj.obj (op U) →+* k) :
    (FibredSite.ringStructureSheafCore B _ hS
      (schemeStack.{u, w} B _ hS (opensObj k B hS U)).val.val.p
      (schemeStack.{u, w} B _ hS (opensObj k B hS U)).val.isFiberedInGroupoids .fppf).obj.obj
      (op (opensArrow.{u, w} k B hS U).left) →+* k :=
  ε.comp (U.topIso.hom.hom.comp (RingHom.id Γ(U.toScheme, ⊤)))

/-- `evalOpens U ε` on the image of a global function `r` of `X` under the ring map at the
terminal arrow is `ε` applied to the restriction of `r` to `U`. -/
lemma evalOpens_pushforwardSectionsRingHom (U : (planesScheme k).Opens)
    (ε : (Spec.structureSheaf (planesRing k)).obj.obj (op U) →+* k) (r : Γ(planesScheme k, ⊤)) :
    evalOpens.{u, w} k B hS U ε
        (pushforwardSectionsRingHom (opensMap.{u, w} k B hS U) (opensArrow.{u, w} k B hS U) r) =
      ε ((planesScheme k).presheaf.map (homOfLE le_top : U ⟶ ⊤).op r) := by
  rw [← topIso_hom_ι_appTop, ← pushforwardSectionsRingHom_opensArrow.{u, w} k B hS U r]
  rfl

/-- **The left hand side of Stacks 0GRN is nonzero** for the two punctured planes `V`, `W` of
`X`: `(V → X)_{QCoh,*}𝒪 ⊗ (W → X)_{QCoh,*}𝒪` is not zero. -/
theorem not_isZero_tensorPushforwardUnits :
    ¬ IsZero (tensorPushforwardUnits (opensMap.{u, w} k B hS (openV k))
      (opensMap.{u, w} k B hS (openW k))) := by
  obtain ⟨hqcV, hqsV⟩ :=
    isQuasiCompactMorphism_and_isQuasiSeparated_opensMap.{u, w} k B hS _ (isCompact_openV k)
  obtain ⟨hqcW, hqsW⟩ :=
    isQuasiCompactMorphism_and_isQuasiSeparated_opensMap.{u, w} k B hS _ (isCompact_openW k)
  have hx₀ := flatObject_schemeStack_id.{u, w} B _ hS (baseObj k B hS)
  obtain ⟨lV, mV, h1V, haddV, hsmulV⟩ := exists_eval_pushforwardUnit _ hqcV hqsV hx₀
    (isTerminalOpensArrow.{u, w} k B hS (openV k)) (evalOpens.{u, w} k B hS _ (evalV k))
  obtain ⟨lW, mW, h1W, haddW, hsmulW⟩ := exists_eval_pushforwardUnit _ hqcW hqsW hx₀
    (isTerminalOpensArrow.{u, w} k B hS (openW k)) (evalOpens.{u, w} k B hS _ (evalW k))
  refine not_isZero_tensorObj_of_eval _ _ (inferInstanceAs (IsAffine (planesScheme k)))
    ((evalOpens.{u, w} k B hS _ (evalV k)).comp
      (pushforwardSectionsRingHom _ (opensArrow.{u, w} k B hS (openV k))))
    lV lW haddV haddW hsmulV (fun r m => ?_) mV mW h1V h1W
  rw [hsmulW]
  congr 1
  change evalOpens.{u, w} k B hS _ (evalW k) (pushforwardSectionsRingHom _ _ r) =
    evalOpens.{u, w} k B hS _ (evalV k) (pushforwardSectionsRingHom _ _ r)
  exact ((evalOpens_pushforwardSectionsRingHom.{u, w} k B hS (openW k) (evalW k) r).trans
    (evalV_res_eq_evalW_res k r).symm).trans
    (evalOpens_pushforwardSectionsRingHom.{u, w} k B hS (openV k) (evalV k) r).symm

/-- **Stacks 0GRN fails for the two punctured planes `V`, `W` of `X`**: for every 2-commutative
square over `(V → X, W → X)` — in particular for the 2-fibre product `V ×_X W` — there is no
isomorphism `(V → X)_{QCoh,*}𝒪_V ⊗ (W → X)_{QCoh,*}𝒪_W ≅ f_{QCoh,*}𝒪_{V ×_X W}`. -/
theorem isEmpty_tensorIso
    (sq : Bicategory.TwoCommSq (opensMap.{u, w} k B hS (openV k))
      (opensMap.{u, w} k B hS (openW k))) :
    IsEmpty (tensorPushforwardUnits (opensMap.{u, w} k B hS (openV k))
        (opensMap.{u, w} k B hS (openW k)) ≅
      pushforwardUnit (sq.fst ≫ opensMap.{u, w} k B hS (openV k))) :=
  ⟨fun e => not_isZero_tensorPushforwardUnits.{u, w} k B hS
    ((isZero_pushforwardUnit_of_isEmpty _ (isEmpty_of_twoCommSq.{u, w} k B hS
      (openV_inf_openW k) sq)).of_iso e)⟩

/-- The counterexample to Stacks 0GRN, with its hypotheses: the open immersions of the two
punctured planes of `X` are representable, quasi-compact, quasi-separated and flat, and for the
2-fibre product there is no isomorphism between the two sides. -/
theorem counterexample :
    Stacks.RepresentableMorphism.IsRepresentableMorphism
        (schemeStack.{u, w} B _ hS (opensObj k B hS (openV k))).val.val.p
        (schemeStack.{u, w} B _ hS (baseObj k B hS)).val.val.p
        (CatFiberedInGroupoids.homFunctor (opensMap.{u, w} k B hS (openV k)).hom) ∧
      IsQuasiCompactMorphism B _ hS (opensMap.{u, w} k B hS (openV k)) ∧
      AlgebraicStacks.IsQuasiSeparated B _ hS (opensMap.{u, w} k B hS (openV k)) ∧
      AlgebraicStacks.IsFlat B _ hS (opensMap.{u, w} k B hS (openV k)) ∧
      Stacks.RepresentableMorphism.IsRepresentableMorphism
        (schemeStack.{u, w} B _ hS (opensObj k B hS (openW k))).val.val.p
        (schemeStack.{u, w} B _ hS (baseObj k B hS)).val.val.p
        (CatFiberedInGroupoids.homFunctor (opensMap.{u, w} k B hS (openW k)).hom) ∧
      IsQuasiCompactMorphism B _ hS (opensMap.{u, w} k B hS (openW k)) ∧
      AlgebraicStacks.IsQuasiSeparated B _ hS (opensMap.{u, w} k B hS (openW k)) ∧
      AlgebraicStacks.IsFlat B _ hS (opensMap.{u, w} k B hS (openW k)) ∧
      IsEmpty (tensorPushforwardUnits (opensMap.{u, w} k B hS (openV k))
          (opensMap.{u, w} k B hS (openW k)) ≅
        pushforwardUnit ((twoFibreProductSquareAlgebraicStacks B _ hS
          (opensMap.{u, w} k B hS (openV k)) (opensMap.{u, w} k B hS (openW k))).fst ≫
            opensMap.{u, w} k B hS (openV k))) :=
  ⟨isRepresentableMorphism_schemeStackMap _,
    (isQuasiCompactMorphism_and_isQuasiSeparated_opensMap.{u, w} k B hS _ (isCompact_openV k)).1,
    (isQuasiCompactMorphism_and_isQuasiSeparated_opensMap.{u, w} k B hS _ (isCompact_openV k)).2,
    isFlat_opensMap.{u, w} k B hS _, isRepresentableMorphism_schemeStackMap _,
    (isQuasiCompactMorphism_and_isQuasiSeparated_opensMap.{u, w} k B hS _ (isCompact_openW k)).1,
    (isQuasiCompactMorphism_and_isQuasiSeparated_opensMap.{u, w} k B hS _ (isCompact_openW k)).2,
    isFlat_opensMap.{u, w} k B hS _, isEmpty_tensorIso.{u, w} k B hS _⟩

end TensorPushforwardPlanes

open _root_.AlgebraicGeometry.Stack.AlgebraicStacks.TensorPushforwardPlanes in
/-- **Stacks 0GRN, as printed, is false.** It is not true that for all 1-morphisms
`a : 𝒴 ⟶ 𝒳`, `b : 𝒵 ⟶ 𝒳` of algebraic stacks which are representable (by schemes),
quasi-compact, quasi-separated and flat,
`a_{QCoh,*}𝒪_𝒴 ⊗_{𝒪_𝒳} b_{QCoh,*}𝒪_𝒵 ≅ f_{QCoh,*}𝒪_{𝒴 ×_𝒳 𝒵}` for the projection
`f : 𝒴 ×_𝒳 𝒵 ⟶ 𝒳` of the 2-fibre product; not even an abstract isomorphism exists in general.

The counterexample: `X = Spec A`, `A = k[x, y, z, w] / (xz, xw, yz, yw)` the union of two planes
meeting at the origin, viewed as an algebraic stack over itself, and `a`, `b` the open immersions
of the punctured planes `V = D(z) ∪ D(w)` and `W = D(x) ∪ D(y)`. They are disjoint, so the right
hand side is `0`, while on global sections the left hand side is
`Γ(V, 𝒪) ⊗_A Γ(W, 𝒪) = k[z, w] ⊗_A k[x, y] = k`. Here `quasicoherentDirectImage` is
`f_{QCoh,*}` of Stacks 077A, `⊗` the tensor product of `QCoh(𝒪_𝒳)` of Stacks 0GQM (the local
instance `fppfModulesMonoidal`, the tensor product sheaf) and `𝟙_` the structure sheaf. The
source's proof breaks at its last step: the
Künneth formula (**Lemma 0FLQ**) computes `Rf_*𝒪 = Ra_*𝒪 ⊗^𝐋 Rb_*𝒪`, and reading off `H⁰` of the
right hand side as `a_*𝒪 ⊗ b_*𝒪` needs `H¹(V, 𝒪) = 0` or flatness; here `H¹(V, 𝒪) ≠ 0` (a punctured
plane) and `Γ(V, 𝒪) = A / (x, y)` is not flat over `A`. The same failure occurs with `a = b` the
open immersion `D(x) ∪ D(z) → Spec k[x, y, z, w] / (xy - zw)`
(`AlgebraicGeometry.TensorPushforwardCounterexample.not_injective_lmul'_coneSections`). The
statement holds when one leg is affine
(`AlgebraicGeometry.Stack.AlgebraicStacks.isIso_tensorPushforwardMap`). -/
@[stacks 0GRN "as printed it is false: a counterexample at X = Spec A, \
  A = k[x,y,z,w]/(xz,xw,yz,yw), with a, b the open immersions of the two punctured planes \
  D(z) ∪ D(w) and D(x) ∪ D(y); the 2-fibre product is empty so f_{QCoh,*}O = 0, while \
  a_{QCoh,*}O ⊗ b_{QCoh,*}O ≠ 0 since Γ(V,O) ⊗_A Γ(W,O) = k (H¹(V,O) ≠ 0 and Γ(V,O) is not A-flat)"]
theorem not_forall_nonempty_tensorPushforwardUnits_iso :
    ¬ ∀ (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
      (𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS) (a : 𝒴 ⟶ 𝒳) (b : 𝒵 ⟶ 𝒳),
      Stacks.RepresentableMorphism.IsRepresentableMorphism 𝒴.val.val.p 𝒳.val.val.p
        (CatFiberedInGroupoids.homFunctor a.hom) →
      IsQuasiCompactMorphism B S hS a → AlgebraicStacks.IsQuasiSeparated B S hS a →
      AlgebraicStacks.IsFlat B S hS a →
      Stacks.RepresentableMorphism.IsRepresentableMorphism 𝒵.val.val.p 𝒳.val.val.p
        (CatFiberedInGroupoids.homFunctor b.hom) →
      IsQuasiCompactMorphism B S hS b → AlgebraicStacks.IsQuasiSeparated B S hS b →
      AlgebraicStacks.IsFlat B S hS b →
      Nonempty ((quasicoherentDirectImage B S hS a).obj (𝟙_ _) ⊗
          (quasicoherentDirectImage B S hS b).obj (𝟙_ _) ≅
        (quasicoherentDirectImage B S hS
          ((twoFibreProductSquareAlgebraicStacks B S hS a b).fst ≫ a)).obj (𝟙_ _)) := by
  intro h
  obtain ⟨B, hS⟩ := BigFppfSite.exists_contains (planesScheme (ULift.{u} ℚ))
  obtain ⟨hrV, hqcV, hqsV, hfV, hrW, hqcW, hqsW, hfW, hE⟩ :=
    TensorPushforwardPlanes.counterexample.{u, w} (ULift.{u} ℚ) B hS
  exact hE.false (h B _ hS _ _ _ _ _ hrV hqcV hqsV hfV hrW hqcW hqsW hfW).some

end AlgebraicGeometry.Stack.AlgebraicStacks
