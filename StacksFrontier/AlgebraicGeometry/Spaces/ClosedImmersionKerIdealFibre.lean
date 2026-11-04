module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SitePointStalkTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModulePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdeals
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicFunctionsPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleNeighborhoodBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkPullbackEtaleLocalRing

/-!
# The kernel of the stalk map of a closed immersion annihilates an annihilated module

Let `i : Z ⟶ X` be a closed immersion of algebraic spaces over a scheme `S` contained in a big
fppf site `B`, let `ℐ = ker(i♯) ⊆ 𝒪_X` be the ideal cutting out `Z`, and let `z̄` be a geometric
point of `Z` with image `x̄ = i ∘ z̄`. Stacks 05V5 attaches to this data a homomorphism
`(𝒪_X)_{x̄} ⟶ (𝒪_Z)_{z̄}` of stalk rings, which after transport to the étale local rings is the
canonical homomorphism of Stacks 04NG. This file proves that its **kernel annihilates the stalk
at `x̄` of every `𝒪_X`-module annihilated by `ℐ`**.

That is the fibrewise form of the annihilation hypothesis, and it is what makes extension of
scalars along the stalk homomorphism harmless on such a module; see
`StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionModuleEssentialImage.lean`, which is the
only consumer.

## Main results

* `AlgebraicGeometry.Space.mem_kerIdeal_structureSharp_iff`: a regular function on an étale
  chart `V` of `X` lies in `ℐ` exactly when its pullback along the cartesian projection
  `Z ×_X V ⟶ V` vanishes.
* `AlgebraicGeometry.Space.smallEtaleStalkPullbackRingMap_germ_baseChange`: the homomorphism of
  stalk rings carries the germ of a regular function on `V` to the germ of that pullback.
* `AlgebraicGeometry.Space.exists_pointed_refinement_mem_kerIdeal`: a regular function whose germ
  is killed by the homomorphism of stalk rings lies in `ℐ` after restriction to a smaller pointed
  chart.
* `AlgebraicGeometry.Space.smul_eq_zero_of_mem_ker_smallEtaleStalkPullbackRingMap`: hence the
  kernel of the homomorphism of stalk rings annihilates the stalk of an `ℐ`-annihilated module.

## Implementation notes

The germ formula and the chartwise description of `ℐ` are about the *same* ring homomorphism —
pullback of regular functions along the cartesian projection `Z ×_X V ⟶ V` — which is what makes
the argument go through: a germ killed by the stalk homomorphism is represented by a function
whose pullback dies on some pointed chart of `Z` over `Z ×_X V`, and that chart has to be replaced
by a base-changed one before the chartwise description applies.

Replacing it is the only geometric input, and it is the cofinality of base change on pointed
charts for a closed immersion: `exists_baseChange_hom` refines the chart of `Z` by a base-changed
one, and `exists_baseChange_factorization` makes the resulting morphism between two base changes
the base change of a morphism of pointed charts of `X`, after one further refinement. Both come
from `StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleNeighborhoodBaseChange.lean`, where they are
the pointed form of Stacks 04E5, part (1) and of Stacks 04FV.

No declaration here carries a Stacks tag attribute: each is a step of the argument rather than an
assertion of the source.

## References

* [Stacks Project, Tag 05V5](https://stacks.math.columbia.edu/tag/05V5)
* [Stacks Project, Tag 04NG](https://stacks.math.columbia.edu/tag/04NG)
* [Stacks Project, Tag 04E5](https://stacks.math.columbia.edu/tag/04E5)
* [Stacks Project, Tag 04FV](https://stacks.math.columbia.edu/tag/04FV)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace Stacks

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C]
  {J : GrothendieckTopology C} (Φ : J.Point.{w}) (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (M : PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat.{w} RingCat.{w}))

/-- **A scalar annihilates a germ as soon as it does so on representatives.** For a point `Φ` of
a site, an element `a` of the stalk of a presheaf of commutative rings and an element `m` of the
stalk of a presheaf of modules over it, `a • m = 0` provided that whenever `a` and `m` are the
germs of a regular function `s` and a section `t` over one common neighbourhood, `s • t`
restricts to zero on some smaller neighbourhood.

Two germs are always represented over one common neighbourhood, and the germ map is semilinear
and compatible with restriction, so `a • m` is the germ of `s • t`. -/
theorem smul_eq_zero_of_exists_refinement (a : ringFiber Φ O) (m : moduleFiber Φ O M)
    (h : ∀ (V : C) (x : Φ.fiber.obj V) (s : O.obj (op V)) (t : M.obj (op V)),
      ringGerm Φ O V x s = a → germ Φ O M V x t = m →
        ∃ (W : C) (c : W ⟶ V) (y : Φ.fiber.obj W), Φ.fiber.map c y = x ∧
          M.restrictₛₗ c.op (s • t) = 0) :
    a • m = 0 := by
  obtain ⟨V₁, x₁, s₁, hs₁⟩ := ringGerm_jointly_surjective (Φ := Φ) (O := O) a
  obtain ⟨V₂, x₂, t₂, ht₂⟩ := germ_jointly_surjective (Φ := Φ) (O := O) (M := M) m
  obtain ⟨V, x, u, v, hu, hv⟩ := exists_common_nbhd (Φ := Φ) x₁ x₂
  have hs : ringGerm Φ O V x (O.map u.op s₁) = a := by
    rw [← ringGerm_w, hu, hs₁]
  have ht : germ Φ O M V x (M.restrictₛₗ v.op t₂) = m := by
    rw [← germ_w, hv, ht₂]
  obtain ⟨W, c, y, hy, hzero⟩ := h V x (O.map u.op s₁) (M.restrictₛₗ v.op t₂) hs ht
  rw [← hs, ← ht, ← germ_smul (Φ := Φ) (O := O) (M := M) V x (O.map u.op s₁)
    (M.restrictₛₗ v.op t₂), ← hy, germ_w, hzero, map_zero]

end Stacks

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z X : AlgebraicSpaces B S hS}

/-- **The kernel ideal, chartwise.** For a representable `i : Z ⟶ X`, a regular function on an
étale scheme chart `V` of `X` lies in the ideal `ℐ = ker(i♯)` cutting out `Z` exactly when its
pullback along the cartesian projection `Z ×_X V ⟶ V` vanishes.

This is `AlgebraicGeometry.Space.ker_structureSharp_eq`, the surjectivity clause of Stacks 03MB,
together with the identification of pullback to the distinguished chart with pullback along the
projection. -/
theorem mem_kerIdeal_structureSharp_iff (i : Z ⟶ X)
    (hi : yoneda.relativelyRepresentable i.hom) (V : SmallEtale B S hS X.1)
    (s : (structureRingSheaf B S hS X).obj.obj (op V)) :
    s ∈ (SheafOfModules.kerIdeal (structureSharp B S hS i)).obj (op V) ↔
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (hi.snd V.1.hom)).op).hom s = 0 := by
  rw [SheafOfModules.mem_kerIdeal, ker_structureSharp_eq B S hS i hi V, RingHom.mem_ker,
    chartPullbackRingHom_chartBaseChangeArrow]
  exact Iff.rfl

/-- **The germ formula on a base-changed chart.** The homomorphism of stalk rings of Stacks 05V5
carries the germ at a lift `q` of `x̄ = i ∘ z̄` of a regular function `s` on an étale scheme chart
`V` of `X` to the germ, at the lift of `z̄` determined by `q`, of the pullback of `s` along the
cartesian projection `Z ×_X V ⟶ V`.

It is the germ formula
`AlgebraicGeometry.Space.smallEtaleStalkPullbackRingMap_toPresheafFiber` applied to
`AlgebraicGeometry.Space.baseChangeChartDiagram` — the commuting square of charts given by base
change, from `StacksFrontier/AlgebraicGeometry/Spaces/MeromorphicFunctionsPushforward.lean`; the
compatibility of the two lifts is that the projection carries the lift of `z̄` back to `q`. -/
theorem smallEtaleStalkPullbackRingMap_germ_baseChange (i : Z ⟶ X)
    (hi : yoneda.relativelyRepresentable i.hom) (z : GeometricPoint B S hS Z.1)
    (V : SmallEtale B S hS X.1)
    (q : GeometricFiber B S hS X.1 (geometricPointMap i.hom z) V)
    (s : (structurePresheaf B S hS X.1).obj (op V)) :
    smallEtaleStalkPullbackRingMap B S hS i z
        ((etaleSitePoint B S hS X.1 (geometricPointMap i.hom z) X.2).toPresheafFiber V q
          (smallEtaleRingedTopos B S hS X).O.obj s) =
      (etaleSitePoint B S hS Z.1 z Z.2).toPresheafFiber
        ((smallBaseChange B S hS i hi).obj V) (smallBaseChangeFiberInv B S hS i hi z V q)
        (structurePresheaf B S hS Z.1)
        (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (hi.snd V.1.hom)).op s) :=
  smallEtaleStalkPullbackRingMap_toPresheafFiber B S hS i z
    (baseChangeChartDiagram B S hS i hi V) (smallBaseChangeFiberInv B S hS i hi z V q) q
    (congrArg Subtype.val
      (smallBaseChangeFiberMap_smallBaseChangeFiberInv B S hS i hi z V q)) s

/-- Pullback of global regular functions along a composite of morphisms of objects of the big
fppf site is the composite of the pullbacks. -/
theorem gamma_toScheme_comp {T₁ T₂ T₃ : BigFppfOver B S hS} (m : T₁ ⟶ T₂) (n : T₂ ⟶ T₃)
    (t : Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj T₃))) :
    (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map m).op).hom
        ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map n).op).hom t) =
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (m ≫ n)).op).hom t := by
  rw [Functor.map_comp, op_comp, Functor.map_comp, CommRingCat.hom_comp, RingHom.coe_comp,
    Function.comp_apply]

/-- **Pullback along the cartesian projection is natural in the chart.** Restricting a regular
function from an étale scheme chart `V` of `X` to a smaller chart `W` and then pulling it back
along `Z ×_X W ⟶ W` is the same as pulling it back along `Z ×_X V ⟶ V` and then restricting along
the base change of `W ⟶ V`.

This is the compatibility `AlgebraicGeometry.Space.smallBaseChange_map_snd` of base change with
the projections, read on regular functions. -/
theorem gamma_snd_naturality (i : Z ⟶ X) (hi : yoneda.relativelyRepresentable i.hom)
    {V W : SmallEtale B S hS X.1} (c : W ⟶ V)
    (s : (smallEtaleRingedTopos B S hS X).O.obj.obj (op V)) :
    (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (hi.snd W.1.hom)).op).hom
        ((smallEtaleRingedTopos B S hS X).O.obj.map c.op s) =
      (structurePresheaf B S hS Z.1).map ((smallBaseChange B S hS i hi).map c).op
        ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (hi.snd V.1.hom)).op).hom s) :=
  (gamma_toScheme_comp B S hS (hi.snd W.1.hom) c.hom.left s).trans
    (((congrArg (fun g ↦ (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map g).op).hom s)
        (smallBaseChange_map_snd B S hS i hi c)).symm).trans
      (gamma_toScheme_comp B S hS ((smallBaseChange B S hS i hi).map c).hom.left
        (hi.snd V.1.hom) s).symm)

/-- Restriction of regular functions on the small étale site along a composite of chart morphisms
is the composite of the restrictions. -/
theorem structurePresheaf_map_comp_apply (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    {A₁ A₂ A₃ : SmallEtale B S hS F} (m : A₁ ⟶ A₂) (n : A₂ ⟶ A₃)
    (t : (structurePresheaf B S hS F).obj (op A₃)) :
    (structurePresheaf B S hS F).map (m ≫ n).op t =
      (structurePresheaf B S hS F).map m.op ((structurePresheaf B S hS F).map n.op t) := by
  rw [op_comp, Functor.map_comp, CategoryTheory.comp_apply]

/-- A regular function restricts to zero along a chart morphism which factors through one along
which it already restricts to zero. -/
theorem structurePresheaf_map_eq_zero_of_factor (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    {A₁ A₂ A₃ : SmallEtale B S hS F} (c : A₁ ⟶ A₃) (m : A₁ ⟶ A₂) (n : A₂ ⟶ A₃)
    (hc : c = m ≫ n) (t : (structurePresheaf B S hS F).obj (op A₃))
    (ht : (structurePresheaf B S hS F).map n.op t = 0) :
    (structurePresheaf B S hS F).map c.op t = 0 := by
  subst hc
  rw [structurePresheaf_map_comp_apply, ht, map_zero]

/-- **The geometric core: a germ killed by the stalk homomorphism is represented by a function in
the kernel ideal.** For a closed immersion `i : Z ⟶ X`, a geometric point `z̄` of `Z`, a pointed
étale scheme chart `(V, q)` of `X` at `x̄ = i ∘ z̄` and a regular function `s` on `V` whose germ is
killed by the homomorphism of stalk rings of Stacks 05V5, there is a smaller pointed chart on
which `s` lies in the ideal `ℐ = ker(i♯)` cutting out `Z`.

By the germ formula the pullback of `s` along `Z ×_X V ⟶ V` has vanishing germ at the lift of
`z̄`, so it restricts to zero on some pointed chart `W` of `Z` over `Z ×_X V`. That chart is
refined by a base-changed one
(`AlgebraicGeometry.Space.SmallEtaleNeighborhood.exists_baseChange_hom`), and the resulting
morphism between two base changes is, after a further refinement, itself a base change
(`AlgebraicGeometry.Space.SmallEtaleNeighborhood.exists_baseChange_factorization`). On that
refinement the pullback of the restricted function factors through `W`, hence vanishes, and
`AlgebraicGeometry.Space.mem_kerIdeal_structureSharp_iff` converts the vanishing into membership
of `ℐ`. -/
theorem exists_pointed_refinement_mem_kerIdeal (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) (z : GeometricPoint B S hS Z.1)
    (V : SmallEtale B S hS X.1)
    (q : GeometricFiber B S hS X.1 (geometricPointMap i.hom z) V)
    (s : (smallEtaleRingedTopos B S hS X).O.obj.obj (op V))
    (hs : smallEtaleStalkPullbackRingMap B S hS i z
      ((etaleSitePoint B S hS X.1 (geometricPointMap i.hom z) X.2).toPresheafFiber V q
        (smallEtaleRingedTopos B S hS X).O.obj s) = 0) :
    ∃ (V' : SmallEtale B S hS X.1) (c : V' ⟶ V)
      (q' : GeometricFiber B S hS X.1 (geometricPointMap i.hom z) V'),
      (geometricFiber B S hS X.1 (geometricPointMap i.hom z)).map c q' = q ∧
        (smallEtaleRingedTopos B S hS X).O.obj.map c.op s ∈
          (SheafOfModules.kerIdeal (structureSharp B S hS i)).obj (op V') := by
  have hzero : (etaleSitePoint B S hS Z.1 z Z.2).toPresheafFiber
      ((smallBaseChange B S hS i hi.rep).obj V)
      (smallBaseChangeFiberInv B S hS i hi.rep z V q) (structurePresheaf B S hS Z.1) 0 = 0 :=
    map_zero _
  obtain ⟨W, h, y, hy, heq⟩ := ((etaleSitePoint B S hS Z.1 z Z.2).toPresheafFiber_eq_iff'
    (P := structurePresheaf B S hS Z.1) ((smallBaseChange B S hS i hi.rep).obj V)
    (smallBaseChangeFiberInv B S hS i hi.rep z V q)
    ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (hi.rep.snd V.1.hom)).op).hom s) 0).1
      (((smallEtaleStalkPullbackRingMap_germ_baseChange B S hS i hi.rep z V q s).symm.trans
        hs).trans hzero.symm)
  obtain ⟨V₀, ⟨k⟩⟩ := SmallEtaleNeighborhood.exists_baseChange_hom B S hS i hi z ⟨W, y.1, y.2⟩
  let hpt : (⟨W, y.1, y.2⟩ : SmallEtaleNeighborhood z) ⟶
      (SmallEtaleNeighborhood.baseChange B S hS i hi.rep z).obj ⟨V, q.1, q.2⟩ :=
    ⟨h, congrArg Subtype.val hy⟩
  obtain ⟨W₁, α, β, hab⟩ := SmallEtaleNeighborhood.exists_baseChange_factorization
    B S hS i hi z V₀ ⟨V, q.1, q.2⟩ (k ≫ hpt)
  have hfac : (smallBaseChange B S hS i hi.rep).map α.hom ≫ (k.hom ≫ h) =
      (smallBaseChange B S hS i hi.rep).map β.hom :=
    congrArg SmallEtaleNeighborhood.Hom.hom hab
  refine ⟨W₁.chart, β.hom, ⟨W₁.point, W₁.point_comp⟩, Subtype.ext β.point_comp, ?_⟩
  have ht1 : (structurePresheaf B S hS Z.1).map (k.hom ≫ h).op
      ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (hi.rep.snd V.1.hom)).op).hom s) = 0 :=
    structurePresheaf_map_eq_zero_of_factor B S hS Z.1 (k.hom ≫ h) k.hom h rfl _
      (heq.trans (map_zero _))
  exact (mem_kerIdeal_structureSharp_iff B S hS i hi.rep W₁.chart _).mpr
    ((gamma_snd_naturality B S hS i hi.rep β.hom s).trans
      (structurePresheaf_map_eq_zero_of_factor B S hS Z.1 _
        ((smallBaseChange B S hS i hi.rep).map α.hom) (k.hom ≫ h) hfac.symm _ ht1))

/-- **The kernel of the stalk homomorphism annihilates the stalk of an annihilated module.** For
a closed immersion `i : Z ⟶ X` of algebraic spaces, a geometric point `z̄` of `Z` and an
`𝒪_X`-module `𝒢` annihilated by the ideal `ℐ = ker(i♯)` cutting out `Z`, every element of the
kernel of the homomorphism `(𝒪_X)_{x̄} ⟶ (𝒪_Z)_{z̄}` of stalk rings of Stacks 05V5 acts as zero on
the stalk of `𝒢` at `x̄ = i ∘ z̄`.

Both the scalar and the module element are germs over one common pointed chart; the previous
statement puts the representing regular function into `ℐ` after a further refinement, where the
sectionwise annihilation hypothesis applies. -/
theorem smul_eq_zero_of_mem_ker_smallEtaleStalkPullbackRingMap (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) (z : GeometricPoint B S hS Z.1)
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : AnnihilatedByKerIdeal B S hS i M)
    (a : Stacks.ringFiber (etaleSitePoint B S hS X.1 (geometricPointMap i.hom z) X.2)
      (smallEtaleRingedTopos B S hS X).O.obj)
    (ha : a ∈ RingHom.ker (smallEtaleStalkPullbackRingMap B S hS i z))
    (m : (Stacks.sheafModuleFiberOfCommRing
        (etaleSitePoint B S hS X.1 (geometricPointMap i.hom z) X.2)
        (smallEtaleRingedTopos B S hS X).O).obj M) :
    a • m = 0 := by
  refine Stacks.smul_eq_zero_of_exists_refinement
    (etaleSitePoint B S hS X.1 (geometricPointMap i.hom z) X.2)
    (smallEtaleRingedTopos B S hS X).O.obj M.val a m ?_
  intro V q s t hsa htm
  obtain ⟨V', c, q', hq', hmem⟩ := exists_pointed_refinement_mem_kerIdeal B S hS i hi z V q s
    ((congrArg (smallEtaleStalkPullbackRingMap B S hS i z) hsa).trans
      (RingHom.mem_ker.1 ha))
  exact ⟨V', c, q', hq',
    (PresheafOfModules.map_smul M.val c.op s t).trans (hM (op V') _ hmem _)⟩

end AlgebraicGeometry.Space

end
