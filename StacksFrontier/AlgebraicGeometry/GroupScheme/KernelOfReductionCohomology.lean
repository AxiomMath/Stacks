module

public import StacksFrontier.CategoryTheory.Sites.SectionwiseKernel
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.BigSiteObjectCohomology
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeRepresentable
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.ChangeOfUniverse
public import StacksFrontier.AlgebraicGeometry.GroupScheme.KernelOfReductionSheaf
public import StacksFrontier.AlgebraicGeometry.Thickenings.KernelOfReductionCohomology

/-!
# The second cohomology of the kernel of reduction of a smooth group scheme

Let `S` be a local affine scheme, `G` a smooth commutative group scheme over `S`, `z : Z ⟶ S`,
and `U` an object of the big fppf site of `S` with `U ×_S Z ⟶ U` a first-order thickening,
`U` Noetherian of dimension at most one. The kernel `K` of `G ⟶ G'`, `G'(T) = G(T ×_S Z)`, has
`H²(U, K) = 0`. This is the vanishing used in part (b) of the proof of [Stacks, Tag 0AFB]: it
makes `H¹(U, G) ⟶ H¹(U, G')` surjective once `G ⟶ G'` is an epimorphism over `U`.

## Main results

* `AlgebraicGeometry.subsingleton_H'_two_of_isLimit_kernel_toBaseChangePushforward_pointsSheaf`.

## Implementation notes

The kernel is taken as an arbitrary limit kernel fork, and the cohomology in an arbitrary `Ext`
universe; the proof passes to the canonical `Ext` universe of the essentially small site by
`CategoryTheory.Abelian.Ext.chgUnivAddEquiv`. The restricted kernel is written as a finite power
of the sectionwise kernel of `Gₐ ⟶ Gₐ'` through
`CategoryTheory.Sheaf.isLimitFanOfBijective`, the sections being matched by the vector-group
isomorphism.

## References

* [Stacks Project, Tag 0AFB](https://stacks.math.columbia.edu/tag/0AFB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u

namespace AlgebraicGeometry

open BigFppfOver

variable (B : BigFppfSite.{u}) {S : Scheme.{u}} (hS : B.Contains S)
  {Z : Scheme.{u}} (hZ : B.Contains Z) (z : B.obj hZ ⟶ B.obj hS)

variable [HasSheafify (BigFppfOver.topology B S hS) AddCommGrpCat.{u}]
  [HasExt.{w} (Sheaf (BigFppfOver.topology B S hS) AddCommGrpCat.{u})]

/-- **The second cohomology of the kernel of reduction of a smooth commutative group scheme
vanishes over a first-order thickening of dimension at most one.** Let `S` be an affine scheme
whose ring of global functions is local, `G` a smooth commutative group scheme over `S`,
`z : Z ⟶ S` a morphism of the big fppf site of `S`, and `U` an object of that site such that
`U ×_S Z ⟶ U` is a first-order thickening and `U` is Noetherian of dimension at most one. If `K`
is the kernel of the map `G ⟶ G'` from the sheaf of points of `G` to its base change along `z`
(sections `T ↦ G(T ×_S Z)`), then `H²(U, K) = 0`.

Over `U` the kernel is a vector group: `K(T) ≅ I_Tᵍ` naturally in `T` over `U`, with
`I_T = ker(Γ(T, 𝒪) → Γ(T ×_S Z, 𝒪))`
(`AlgebraicGeometry.exists_addEquiv_ker_toBaseChangePushforward_pointsSheaf`). Restricting to
the big fppf site of `U` along `Over.map` does not change cohomology over `U`
(`Stacks.Cohomology.BiggerSite.cohomologyPresheafFunctorIso`), and there `H²` of a finite power
of the kernel of reduction of `Gₐ` vanishes
(`AlgebraicGeometry.BigFppfOver.subsingleton_H'_of_isLimit_fan_kernel_additiveGroupSheaf`). -/
theorem subsingleton_H'_two_of_isLimit_kernel_toBaseChangePushforward_pointsSheaf [IsAffine S]
    [IsLocalRing Γ(S, ⊤)] (G : Over S) [GrpObj G] [IsCommMonObj G] [Smooth G.hom]
    (hG : B.Contains G.left) (U : BigFppfOver B S hS)
    (hU : Stacks.Thickenings.IsFirstOrderThickening
      (B.inclusion.map (Sheaf.baseChangeFst z U).left))
    [IsNoetherian (B.inclusion.obj U.left)]
    (hdim : topologicalKrullDim (B.inclusion.obj U.left : Type u) ≤ 1)
    (K : Sheaf (BigFppfOver.topology B S hS) AddCommGrpCat.{u})
    (ι : K ⟶ pointsSheaf B S hS G hG)
    (w : ι ≫ (pointsSheaf B S hS G hG).toBaseChangePushforward z = 0)
    (hK : IsLimit (KernelFork.ofι ι w)) :
    Subsingleton (Sheaf.H' K 2 U) := by
  obtain ⟨g, θ, hθ⟩ := exists_addEquiv_ker_toBaseChangePushforward_pointsSheaf B hS hZ z G hG U hU
  -- the base `X` of the restriction and the restriction functor `Φ`
  let X : Scheme.{u} := B.inclusion.obj U.left
  have hX : B.Contains X := U.left.2
  let f : B.obj hX ⟶ B.obj hS := U.hom
  let Φ := Over.map f
  let JX := BigFppfOver.topology B X hX
  let JS := BigFppfOver.topology B S hS
  -- canonical `Ext` universes on both sites
  have ext0 : HasExt.{u} (Sheaf JS AddCommGrpCat.{u}) :=
    Stacks.Cohomology.FreeYonedaUnivLE.hasExt_essentiallySmallSite JS
  have ext1 : HasExt.{u} (Sheaf JX AddCommGrpCat.{u}) :=
    Stacks.Cohomology.FreeYonedaUnivLE.hasExt_essentiallySmallSite JX
  -- the restricted kernel and its decomposition
  let P := (Φ.sheafPushforwardContinuous AddCommGrpCat.{u} JX JS).obj K
  let φX := (Φ.sheafPushforwardContinuous AddCommGrpCat.{u} JX JS).map
    ((BigFppfOver.additiveGroupSheaf S B hS).toBaseChangePushforward z)
  have hP : Subsingleton (Sheaf.H'.{u} P 2 (Over.mk (𝟙 (B.obj hX)))) := by
    let t : ∀ T : BigFppfOver B X hX, Φ.obj T ⟶ U := fun T => Over.homMk T.hom rfl
    have ht : ∀ {T T' : BigFppfOver B X hX} (g : T ⟶ T'), Φ.map g ≫ t T' = t T := by
      intro T T' g
      ext1
      exact Over.w g
    have hθc : ∀ (T : BigFppfOver B S hS) (t t' : T ⟶ U)
        (a a' : (((pointsSheaf B S hS G hG).toBaseChangePushforward z).hom.app (op T)).hom.ker),
        t = t' → (a : (pointsSheaf B S hS G hG).obj.obj (op T)) = a' →
          θ T t a = θ T t' a' := by
      intro T t t' a a' h1 h2
      subst h1
      rw [Subtype.ext h2]
    let ρ : ∀ T : BigFppfOver B X hX, K.obj.obj (op (Φ.obj T)) →+
        (((pointsSheaf B S hS G hG).toBaseChangePushforward z).hom.app (op (Φ.obj T))).hom.ker :=
      fun T => (ι.hom.app (op (Φ.obj T))).hom.codRestrict _ (fun x => by
        rw [AddMonoidHom.mem_ker]
        exact DFunLike.congr_fun (congrArg AddCommGrpCat.Hom.hom
          (congrArg (fun g => g.hom.app (op (Φ.obj T))) w)) x)
    let π : Fin g → (P ⟶ Sheaf.sectionwiseKernel φX) := fun k => ⟨{
      app := fun T => AddCommGrpCat.ofHom ((Pi.evalAddMonoidHom _ k).comp
        ((θ (Φ.obj T.unop) (t T.unop)).toAddMonoidHom.comp (ρ T.unop)))
      naturality := fun T T' g' => by
        ext x
        apply Subtype.ext
        have hnat : (ι.hom.app (op (Φ.obj T'.unop))).hom ((K.obj.map (Φ.map g'.unop).op).hom x) =
            ((pointsSheaf B S hS G hG).obj.map (Φ.map g'.unop).op).hom
              ((ι.hom.app (op (Φ.obj T.unop))).hom x) :=
          DFunLike.congr_fun (congrArg AddCommGrpCat.Hom.hom
            (ι.hom.naturality (Φ.map g'.unop).op)) x
        have ha : (ι.hom.app (op (Φ.obj T.unop))).hom x ∈
            (((pointsSheaf B S hS G hG).toBaseChangePushforward z).hom.app
              (op (Φ.obj T.unop))).hom.ker := (ρ T.unop x).2
        have ha' : ((pointsSheaf B S hS G hG).obj.map (Φ.map g'.unop).op).hom
            ((ι.hom.app (op (Φ.obj T.unop))).hom x) ∈
            (((pointsSheaf B S hS G hG).toBaseChangePushforward z).hom.app
              (op (Φ.obj T'.unop))).hom.ker := by
          rw [← hnat]
          exact (ρ T'.unop ((K.obj.map (Φ.map g'.unop).op).hom x)).2
        have key := hθ (Φ.obj T.unop) (Φ.obj T'.unop) (t T.unop) (Φ.map g'.unop) _ ha ha' k
        have key2 : θ (Φ.obj T'.unop) (t T'.unop)
            (ρ T'.unop ((K.obj.map (Φ.map g'.unop).op).hom x)) =
            θ (Φ.obj T'.unop) (Φ.map g'.unop ≫ t T.unop) ⟨_, ha'⟩ :=
          hθc _ _ _ _ _ (ht g'.unop).symm hnat
        change (θ (Φ.obj T'.unop) (t T'.unop)
            (ρ T'.unop ((K.obj.map (Φ.map g'.unop).op).hom x)) k).1 =
          ((BigFppfOver.additiveGroupSheaf S B hS).obj.map (Φ.map g'.unop).op).hom
            (θ (Φ.obj T.unop) (t T.unop) (ρ T.unop x) k).1
        rw [key2]
        exact key }⟩
    have hbij : ∀ T, Function.Bijective (Sheaf.piSectionsHom π T) := by
      intro T
      have : ⇑(Sheaf.piSectionsHom π T) = ⇑(θ (Φ.obj T.unop) (t T.unop)) ∘ ⇑(ρ T.unop) := rfl
      rw [this]
      exact (θ _ _).bijective.comp
        (Sheaf.bijective_codRestrict_of_isLimit _ ι w hK (op (Φ.obj T.unop)))
    exact subsingleton_H'_of_isLimit_fan_kernel_additiveGroupSheaf.{u} B hS hZ z hX f hU.1 hdim
      (Sheaf.sectionwiseKernel φX)
      (Sheaf.sectionwiseKernelι φX) (Sheaf.sectionwiseKernelι_comp φX)
      (Sheaf.isLimitSectionwiseKernel φX) P π (Sheaf.isLimitFanOfBijective π hbij) 2 le_rfl
  have : HasFiniteLimits (BigFppfOver B X hX) := hasFiniteLimits_of_hasTerminal_and_pullbacks
  have e1 : Sheaf.H'.{u} P 2 (Over.mk (𝟙 (B.obj hX))) ≅
      Sheaf.H'.{u} K 2 (Φ.obj (Over.mk (𝟙 (B.obj hX)))) :=
    (Stacks.Cohomology.BiggerSite.cohomologyPresheafFunctorIso JX JS Φ
      (Over.mk (𝟙 (B.obj hX))) 2).app K
  have e2 : Φ.obj (Over.mk (𝟙 (B.obj hX))) ≅ U := Over.isoMk (Iso.refl _) (by simp [Φ, f])
  have e3 : Sheaf.H'.{u} K 2 U ≅ Sheaf.H'.{u} K 2 (Φ.obj (Over.mk (𝟙 (B.obj hX)))) :=
    (K.cohomologyPresheaf 2).mapIso e2.op
  have hu : Subsingleton (Sheaf.H'.{u} K 2 U) :=
    (e3 ≪≫ e1.symm).addCommGroupIsoToAddEquiv.toEquiv.subsingleton_congr.mpr hP
  exact (Abelian.Ext.chgUnivAddEquiv.{u, w}).toEquiv.subsingleton_congr.mp hu

end AlgebraicGeometry
