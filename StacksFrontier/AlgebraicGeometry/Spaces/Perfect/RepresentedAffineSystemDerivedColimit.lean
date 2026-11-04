module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitDerivedHomAffineLeafHomEquivFactor
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitDerivedHomAffineLeafRepresentedCrossing
public import StacksFrontier.AlgebraicGeometry.Perfect.LimitHomDescent.TotalDerivedTranspose
public import StacksFrontier.AlgebraicGeometry.Perfect.LimitHomDescent.LimitDerivedHomAffineLeafZariskiSingleDegree
public import StacksFrontier.AlgebraicGeometry.Perfect.LimitHomDescent.AffineObjects

/-!
# The affine case of Stacks 09RI at the structure sheaf and a quasi-coherent object

Let `V_j` be a directed system of affine representables over an affine representable `V₀`, with
a cone `V` whose rings of global functions are the filtered colimit of those of the `V_j`
(`AlgebraicGeometry.Space.RepresentedAffineSystem`), and write `R = Γ(V₀, 𝒪)`,
`A_j = Γ(V_j, 𝒪)`, `A = Γ(V, 𝒪)`.  For a complex `P` of finitely presented `R`-modules with
finitely many nonzero terms, each `A_j ⊗_R P` K-projective, and a K-flat complex `N` of
`R`-modules, this file proves

`Hom(Lk^*Φ(P), Lk^*Φ(N)) = colim_j Hom(Lk_j^*Φ(P), Lk_j^*Φ(N))`,

`Φ` the derived associated-module functor of Stacks 08H1, the derived pullbacks taken with their
canonical pseudofunctoriality.  At `P = R[q]` this is the colimit statement at the structure sheaf
in degree `q` and an *arbitrary* object of `D_QCoh(𝒪_{h_{V₀}})`, every such object being some
`Φ(N)`.

The proof reads the system of homomorphism groups through the bijection of Stacks 08H1 and the
identification of the chosen derived extensions of scalars with the termwise ones at K-flat
complexes: the groups become `Hom_{K(R)}(P, A_j ⊗_R N)` over the one ring `R`
(`Stacks.LimitHomDescent.Affine.totalDerivedTranspose`), their transition maps become
post-composition with the base-change maps `A_i ⊗_R N ⟶ A_j ⊗_R N`
(`Stacks.LimitHomDescent.Affine.totalDerivedTranspose_comp_tau` against
`AlgebraicGeometry.Space.representedAffineDerivedPullbackHomEquiv_factorHom`), and the colimit
statement is `Stacks.LimitHomDescent.isStagesColimit_homotopy`, the ring-level core of
Stacks 09RE.

## Main definitions

* `AlgebraicGeometry.Space.RepresentedAffineSystem.ringSystem`: the directed system of rings of
  global functions of a represented affine system, as a `Stacks.LimitHomDescent.Affine.RingSystem`.

## Main results

* `AlgebraicGeometry.Space.RepresentedAffineSystem.isColim_derivedAssociated`: **the colimit
  statement at `Φ(P)` and `Φ(N)`**.
* `AlgebraicGeometry.Space.RepresentedAffineSystem.isColim_unitObj_derivedAssociated`:
  **the colimit statement at the structure sheaf in any degree and an arbitrary derived associated
  module**, hence at an arbitrary object of `D_QCoh(𝒪_{h_{V₀}})`.

## Implementation notes

`AlgebraicGeometry.Space.RepresentedAffineSystem` does not record that the transition morphism
of `i ≤ i` is the identity; the statements here take it as the hypothesis `hid`.  It is a
property of the system, not of the colimit, and it holds for every system built from a functor.

## References

* [Stacks Project, Lemma 75.24.2 (Tag 09RI)](https://stacks.math.columbia.edu/tag/09RI)
* [Stacks Project, Lemma 36.29.2 (Tag 09RE)](https://stacks.math.columbia.edu/tag/09RE)
* [Stacks Project, Lemma 75.13.6 (Tag 08H1)](https://stacks.math.columbia.edu/tag/08H1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.FilteredColimitHom (Qh)
open Stacks.LimitHomDescent.Affine (ext resExt tau totalDerivedTranspose)

universe w u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

attribute [local instance] additive_extendScalars_representedAffineRingHom
  additive_pullbackModules_representedSpaceMap

attribute [local instance 6000] preadditive_smallEtaleModules

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The bijection of 08H1 along a factorisation through a given composite -/

section HomEquiv

variable {U U' U'' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U'')]

/-- `AlgebraicGeometry.Space.representedAffineDerivedPullbackHomEquiv_factorHom` for a
factorisation `g₂ ≫ g = k` through a given composite `k`. -/
theorem representedAffineDerivedPullbackHomEquiv_factorHom_of_eq (g : U' ⟶ U) (g₂ : U'' ⟶ U')
    (k : U'' ⟶ U) (hk : g₂ ≫ g = k)
    (hk' : representedSpaceMap B S hS g₂ ≫ representedSpaceMap B S hS g =
      representedSpaceMap B S hS k)
    (hc : (representedAffineCommRingCatHom B S hS g₂).hom.comp
      (representedAffineCommRingCatHom B S hS g).hom =
        (representedAffineCommRingCatHom B S hS k).hom)
    (M N : DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)))
    (φ : (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g)).obj
          ((representedAffineDerivedAssociated B S hS U).obj M) ⟶
        (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g)).obj
          ((representedAffineDerivedAssociated B S hS U).obj N)) :
    representedAffineDerivedPullbackHomEquiv B S hS k M N
        ((canonicalPullbackData B S hS).factorHom hk' φ) =
      (RingTheory.TorIndependence.totalDerivedExtensionScalarsCompOfEq
          (representedAffineCommRingCatHom B S hS g).hom
          (representedAffineCommRingCatHom B S hS g₂).hom
          (representedAffineCommRingCatHom B S hS k).hom hc).inv.app M ≫
        (representedAffineDerivedExtension B S hS g₂).functor.map
          (representedAffineDerivedPullbackHomEquiv B S hS g M N φ) ≫
        (RingTheory.TorIndependence.totalDerivedExtensionScalarsCompOfEq
          (representedAffineCommRingCatHom B S hS g).hom
          (representedAffineCommRingCatHom B S hS g₂).hom
          (representedAffineCommRingCatHom B S hS k).hom hc).hom.app N := by
  subst hk
  exact representedAffineDerivedPullbackHomEquiv_factorHom B S hS g g₂ M N φ

end HomEquiv

namespace RepresentedAffineSystem

variable {V₀ : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj V₀)]
  {J : Type w} [Preorder J] (Sys : RepresentedAffineSystem V₀ J)

/-- The ring map on global functions induced by a composite `a ≫ b` of morphisms between
represented affine objects is the composite of the ring maps induced by `b` and by `a`. -/
theorem representedAffineCommRingCatHom_comp {U U' U'' : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U'')] (a : U'' ⟶ U') (b : U' ⟶ U) :
    representedAffineCommRingCatHom B S hS (a ≫ b) =
      representedAffineCommRingCatHom B S hS b ≫ representedAffineCommRingCatHom B S hS a :=
  CommRingCat.hom_ext (representedAffineRingHom_comp B S hS a b)

/-- **The rings of global functions of a represented affine system**, as a directed system of
`Γ(V₀, 𝒪)`-algebras with the cocone of the rings of global functions of the vertex. -/
def ringSystem (hid : ∀ i : J, Sys.map (le_refl i) = 𝟙 _) :
    Stacks.LimitHomDescent.Affine.RingSystem.{w, u} Γ((BigFppfOver.toScheme B S hS).obj V₀, ⊤)
      J where
  A j := Γ((BigFppfOver.toScheme B S hS).obj (Sys.obj j), ⊤)
  φ j := representedAffineCommRingCatHom B S hS (Sys.toBase j)
  β h := representedAffineCommRingCatHom B S hS (Sys.map h)
  φ_β h := by rw [← representedAffineCommRingCatHom_comp, Sys.map_toBase]
  β_β h h' := by rw [← representedAffineCommRingCatHom_comp, Sys.map_comp]
  β_refl i := by
    rw [hid]
    exact CommRingCat.hom_ext (by
      simp [representedAffineCommRingCatHom])
  lim := Γ((BigFppfOver.toScheme B S hS).obj Sys.lim, ⊤)
  φlim := representedAffineCommRingCatHom B S hS Sys.limToBase
  γ j := representedAffineCommRingCatHom B S hS (Sys.proj j)
  φ_γ j := by rw [← representedAffineCommRingCatHom_comp, Sys.proj_toBase]
  β_γ h := by rw [← representedAffineCommRingCatHom_comp, Sys.proj_map]

variable (hid : ∀ i : J, Sys.map (le_refl i) = 𝟙 _)
  (P N : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj V₀, ⊤)) ℤ)
  (hP : P.KFlat) (hN : N.KFlat)

/-- The identification of the homomorphism group of a stage of the system with
`Hom_{K(R)}(P, A_j ⊗_R N)`: the bijection of Stacks 08H1 followed by the inverse of
`Stacks.LimitHomDescent.Affine.totalDerivedTranspose`. -/
def stageHomEquiv {U : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    (g : U ⟶ V₀) [((ext (representedAffineCommRingCatHom B S hS g)).obj P).IsKProjective] :
    ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g)).obj
          ((representedAffineDerivedAssociated B S hS V₀).obj (DerivedCategory.Q.obj P)) ⟶
        (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g)).obj
          ((representedAffineDerivedAssociated B S hS V₀).obj (DerivedCategory.Q.obj N))) ≃
      ((Qh _).obj P ⟶ (Qh _).obj
        (((resExt (representedAffineCommRingCatHom B S hS g)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj N)) :=
  (representedAffineDerivedPullbackHomEquiv B S hS g _ _).trans
    (Equiv.ofBijective _ (Stacks.LimitHomDescent.Affine.totalDerivedTranspose_bijective P N hP hN
      (representedAffineCommRingCatHom B S hS g))).symm

/-- For `g₂ ≫ g = k`, `stageHomEquiv` at `k` of the morphism factored through `g₂` is
`stageHomEquiv` at `g` followed by the image under `Qh` of the map of complexes
`A_g ⊗_R N ⟶ A_k ⊗_R N` induced by the ring map of `g₂`. -/
theorem stageHomEquiv_factorHom {U U' : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U')] (g : U ⟶ V₀) (g₂ : U' ⟶ U) (k : U' ⟶ V₀)
    (hk : g₂ ≫ g = k)
    (hk' : representedSpaceMap B S hS g₂ ≫ representedSpaceMap B S hS g =
      representedSpaceMap B S hS k)
    [((ext (representedAffineCommRingCatHom B S hS g)).obj P).IsKProjective]
    [((ext (representedAffineCommRingCatHom B S hS k)).obj P).IsKProjective]
    (φ : (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g)).obj
          ((representedAffineDerivedAssociated B S hS V₀).obj (DerivedCategory.Q.obj P)) ⟶
        (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g)).obj
          ((representedAffineDerivedAssociated B S hS V₀).obj (DerivedCategory.Q.obj N))) :
    stageHomEquiv P N hP hN k ((canonicalPullbackData B S hS).factorHom hk' φ) =
      stageHomEquiv P N hP hN g φ ≫ (Qh _).map ((NatTrans.mapHomologicalComplex
        (tau (representedAffineCommRingCatHom B S hS g) (representedAffineCommRingCatHom B S hS k)
          (representedAffineCommRingCatHom B S hS g₂)
          (by rw [← representedAffineCommRingCatHom_comp, hk])) (ComplexShape.up ℤ)).app N) := by
  have hc : (representedAffineCommRingCatHom B S hS g₂).hom.comp
      (representedAffineCommRingCatHom B S hS g).hom =
        (representedAffineCommRingCatHom B S hS k).hom := by
    rw [← representedAffineRingHom_comp, hk]
  simp only [stageHomEquiv, Equiv.coe_trans, Function.comp_apply]
  refine (Equiv.symm_apply_eq _).2 ?_
  change representedAffineDerivedPullbackHomEquiv B S hS k _ _ _ =
    totalDerivedTranspose P N hP hN _ _
  rw [Stacks.LimitHomDescent.Affine.totalDerivedTranspose_comp_tau P N hP hN _ _ _ _ hc,
    representedAffineDerivedPullbackHomEquiv_factorHom_of_eq g g₂ k hk hk' hc]
  congr 2
  exact congrArg _ (Equiv.ofBijective_apply_symm_apply _ _ _).symm

include hid hP hN in
/-- **The affine case of Stacks 09RE–09RI at derived associated modules.**  Along a directed
system of affine representables over `V₀` whose rings of global functions form a filtered colimit,
for a complex `P` of finitely presented `R`-modules with finitely many nonzero terms and every
`A_j ⊗_R P` and `A ⊗_R P` K-projective, and a K-flat complex `N`,

`Hom(Lk^*Φ(P), Lk^*Φ(N)) = colim_j Hom(Lk_j^*Φ(P), Lk_j^*Φ(N))`,

the derived pullbacks taken with `AlgebraicGeometry.Space.canonicalPullbackData`. -/
theorem isColim_derivedAssociated [IsDirected J (· ≤ ·)] [Nonempty J] (hring : Sys.IsRingColimit)
    [∀ j, ((ext (representedAffineCommRingCatHom B S hS (Sys.toBase j))).obj P).IsKProjective]
    [((ext (representedAffineCommRingCatHom B S hS Sys.limToBase)).obj P).IsKProjective]
    (W : Finset ℤ) (hW : ∀ n : ℤ, n ∉ W → IsZero (P.X n))
    (hfp : ∀ n : ℤ, Module.FinitePresentation Γ((BigFppfOver.toScheme B S hS).obj V₀, ⊤) (P.X n)) :
    Sys.toLimitSystem.IsColim (canonicalPullbackData B S hS)
      ((representedAffineDerivedAssociated B S hS V₀).obj (DerivedCategory.Q.obj P))
      ((representedAffineDerivedAssociated B S hS V₀).obj (DerivedCategory.Q.obj N)) := by
  let RS := Sys.ringSystem hid
  have hst := RS.isStagesColimit_stageCx N hring
  have heart := Stacks.LimitHomDescent.isStagesColimit_homotopy (E := P)
    (fun _ _ _ h h' => RS.tcx_comp N h h') (fun _ _ h => RS.tcx_ιcx N h)
    (fun n x => (hst n).exists_stage x)
    (fun n j y hy => by
      obtain ⟨k, h, hk⟩ := (hst n).exists_trans_eq j y 0 (hy.trans (map_zero _).symm)
      exact ⟨k, h, hk.trans (map_zero _)⟩) W (fun n hn => Or.inl (hW n hn)) hfp
  exact Stacks.IsStagesColimit.ofEquiv _ _
    (fun j => stageHomEquiv P N hP hN (Sys.toBase j)) (stageHomEquiv P N hP hN Sys.limToBase)
    (fun i j h s => stageHomEquiv_factorHom P N hP hN (Sys.toBase i) (Sys.map h) (Sys.toBase j)
      (Sys.map_toBase h) _ s)
    (fun i s => stageHomEquiv_factorHom P N hP hN (Sys.toBase i) (Sys.proj i) Sys.limToBase
      (Sys.proj_toBase i) _ s)
    heart

/-- The complex `R[j]` is K-flat. -/
private theorem kFlat_single_self (R : CommRingCat.{u}) (j : ℤ) :
    CochainComplex.KFlat ((HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) j).obj
      (ModuleCat.of R R)) := by
  let K :=
    (HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) j).obj (ModuleCat.of R R)
  have (i : ℤ) : Module.Flat R (K.X i) := by
    by_cases hi : i = j
    · exact Module.Flat.of_linearEquiv
        (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) j
          (ModuleCat.of R R) i hi).toLinearEquiv
    · exact Module.Flat.of_linearEquiv
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) j
          (ModuleCat.of R R) i hi).isoZero.toLinearEquiv
  exact CochainComplex.KFlat.kFlat_of_flat K j

include hid in
/-- **The affine case of Stacks 09RI at the structure sheaf and a derived associated module.**
Along a directed system of affine representables over `V₀` whose rings of global functions form
a filtered colimit, for every `p` and every object `N` of `D(R)`, `R = Γ(V₀, 𝒪)`,

`Hom(Lk^*𝒪[p], Lk^*Φ(N)) = colim_j Hom(Lk_j^*𝒪[p], Lk_j^*Φ(N))`,

the derived pullbacks taken with `AlgebraicGeometry.Space.canonicalPullbackData`.  Every object
of `D_QCoh(𝒪_{h_{V₀}})` is some `Φ(N)`
(`AlgebraicGeometry.Space.exists_iso_representedAffineDerivedAssociated_of_qcohDerived`).

`N` has a K-flat model and `𝒪[p]` is `Φ(R[p])`, so this is
`AlgebraicGeometry.Space.RepresentedAffineSystem.isColim_derivedAssociated` at `P = R[p]`. -/
theorem isColim_unitObj_derivedAssociated [IsDirected J (· ≤ ·)] [Nonempty J]
    (hring : Sys.IsRingColimit) (p : ℤ)
    (N : DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj V₀, ⊤))) :
    Sys.toLimitSystem.IsColim (canonicalPullbackData B S hS)
      (representedAffineUnitObj B S hS V₀ p)
      ((representedAffineDerivedAssociated B S hS V₀).obj N) := by
  have hcoh := (DerivedPullbackComposition.canonical B S hS).isCoherent_toPullbackData
  obtain ⟨C, hC, ⟨eC⟩⟩ := Stacks.LimitHomDescent.Affine.RingSystem.exists_kFlat_iso N
  have hK : ∀ {U : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
      (g : U ⟶ V₀), ((ext (representedAffineCommRingCatHom B S hS g)).obj
        ((HomologicalComplex.single (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj V₀, ⊤))
          (ComplexShape.up ℤ) p).obj
          (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj V₀, ⊤)
            Γ((BigFppfOver.toScheme B S hS).obj V₀, ⊤)))).IsKProjective :=
    fun g => Stacks.LimitHomDescent.Affine.isKProjective_ext_singleDegree _ p
  have := fun j => hK (Sys.toBase j)
  have := hK Sys.limToBase
  have key := Sys.isColim_derivedAssociated hid _ C (kFlat_single_self _ p) hC hring {p}
    (fun m hm => HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) p _ m
      (by simpa using hm))
    (Stacks.LimitHomDescent.Affine.finitePresentation_singleDegree_X _ p)
  exact (key.of_iso_fst hcoh ((representedAffineDerivedAssociated B S hS V₀).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ _ p).app _).symm)).of_iso_snd hcoh _
    ((representedAffineDerivedAssociated B S hS V₀).mapIso eC)

end RepresentedAffineSystem

end AlgebraicGeometry.Space

end
