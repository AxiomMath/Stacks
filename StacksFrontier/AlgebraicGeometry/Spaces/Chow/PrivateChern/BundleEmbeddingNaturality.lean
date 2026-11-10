module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.BundleBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.BundleEmbedding
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.SymGenNatural
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine
public import StacksFrontier.AlgebraicGeometry.PullbackTensor.UniversalGradedAlgebra
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.BaseChangeCompAlgebra
public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.ProjectiveBundleBaseChange
public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.Functoriality
public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.ProjectiveBundleBaseChangeComp

/-!
# The closed immersion of projective bundles commutes with base change

Let `g : X' ⟶ X` be a morphism of schemes, `q : ℰ ⟶ ℱ` an epimorphism of finite locally free
`𝒪_X`-modules and `q' : ℰ' ⟶ ℱ'` one of `𝒪_{X'}`-modules, with identifications `ℰ' ≅ g^*ℰ` and
`ℱ' ≅ g^*ℱ` carrying `q'` to `g^*q`. Then the closed immersions `𝐏(ℱ) ⟶ 𝐏(ℰ)` and
`𝐏(ℱ') ⟶ 𝐏(ℰ')` induced by `q` and `q'` (`Stacks.Chow.GenuineChern.bundleEmbedding`) commute
with the base-change morphisms `𝐏(ℰ') ⟶ 𝐏(ℰ)` and `𝐏(ℱ') ⟶ 𝐏(ℱ)` of Stacks 01O3.

On the charts over affine opens `W' ⊆ g⁻¹W` both composites are `Proj` of a homomorphism of
graded rings of sections `Γ(W, Sym ℰ) ⟶ Γ(W', Sym ℱ')`, and the two homomorphisms agree because
both come from homomorphisms of graded algebras `g^*Sym(ℰ) ⟶ Sym(ℱ')` agreeing on the degree-one
generator, `g^*Sym(ℰ)` being a symmetric algebra on `g^*ℰ` (Stacks 01CI).

## Main results

* `AlgebraicGeometry.Space.PrivateChern.symUnitalHom`: the homomorphism `Sym(ℰ) ⟶ Sym(ℱ)` of a
  morphism `ℰ ⟶ ℱ`, as a unital homomorphism of graded algebras.
* `AlgebraicGeometry.Space.PrivateChern.symmetricSituationPullbackHom_comp_symUnitalHom`: the
  two homomorphisms `g^*Sym(ℰ) ⟶ Sym(ℱ')` agree.

## References

* [Stacks Project, Tag 01CI](https://stacks.math.columbia.edu/tag/01CI)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open SheafOfModules.GradedAlgebra
open Stacks.AlgebraicGeometry.ModuleLimits Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

universe u

namespace AlgebraicGeometry.Space.PrivateChern

section Algebra

variable {X : Scheme.{u}} {E F : X.Modules}

/-- The homomorphism `Sym(ℰ) ⟶ Sym(ℱ)` induced by `u : ℰ ⟶ ℱ`, as a unital homomorphism of
graded algebras. -/
def symUnitalHom (u : E ⟶ F) :
    UnitalHom (Scheme.Modules.symmetricAlgebra X E) (Scheme.Modules.symmetricAlgebra X F) where
  app n := (Stacks.SymGraded.schemeSymAlgebraHom u).app n
  map_mul i j U a b := (Stacks.SymGraded.schemeSymAlgebraHom u).map_mul i j U a b
  map_one U := Stacks.SymGraded.schemeSymAlgebraHom_app_one u U

/-- The generator `ℰ ⟶ Sym¹(ℰ)` of the symmetric algebra of a module on a scheme is the generator
of the sheafified symmetric algebra for the Zariski topology. -/
theorem symmetricAlgebraGen_eq_sheafifiedSymmetricGenerator (E : X.Modules) :
    Scheme.Modules.symmetricAlgebraGen X E =
      SheafOfModules.sheafifiedSymmetricGenerator (Opens.grothendieckTopology ↥X) E :=
  rfl

end Algebra

section PullbackAlgebra

variable {X X' : Scheme.{u}} (g : X' ⟶ X) {E F : X.Modules} [E.IsQuasicoherent]
  [F.IsQuasicoherent] {E' F' : X'.Modules} [E'.IsQuasicoherent] [F'.IsQuasicoherent]
  (q : E ⟶ F) (q' : E' ⟶ F') (cE : E' ≅ (Scheme.Modules.pullback g).obj E)
  (cF : F' ≅ (Scheme.Modules.pullback g).obj F)

/-- **The two homomorphisms `g^*Sym(ℰ) ⟶ Sym(ℱ')` agree**, when `q'` is `g^*q` through the
identifications: both are unital homomorphisms out of the symmetric algebra `g^*Sym(ℰ)` on
`g^*ℰ`, and they agree on its generator. -/
theorem symmetricSituationPullbackHom_comp_symUnitalHom
    (hc : q' ≫ cF.hom = cE.hom ≫ (Scheme.Modules.pullback g).map q) :
    (Stacks.RelativeProj.symmetricSituationPullbackHom g E E' cE).comp (symUnitalHom q') =
      (baseAlgebraMapHom g (symUnitalHom q)).comp
        (Stacks.RelativeProj.symmetricSituationPullbackHom g F F' cF) := by
  have hA := Stacks.RingedSpace.isSymmetricAlgebra_pullbackGradedAlgebra g.toLRSHom.toShHom
    (SheafOfModules.isSymmetricAlgebra_sheafifiedSymmetricAlgebra (Opens.grothendieckTopology ↥X) E)
  set γE := SheafOfModules.sheafifiedSymmetricGenerator (Opens.grothendieckTopology ↥X) E
  set γF := SheafOfModules.sheafifiedSymmetricGenerator (Opens.grothendieckTopology ↥X) F
  set γF' := SheafOfModules.sheafifiedSymmetricGenerator (Opens.grothendieckTopology ↥X') F'
  have hc' : cE.inv ≫ q' = (Scheme.Modules.pullback g).map q ≫ cF.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← hc, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have hgenE := Stacks.SymmetricAlgebra.pullbackSheafifiedPieceIsoOfIso_generator g E E' cE
  have hgenF := Stacks.SymmetricAlgebra.pullbackSheafifiedPieceIsoOfIso_generator g F F' cF
  have hq : γE ≫ (symUnitalHom q).app 1 = q ≫ γF :=
    Stacks.Chow.GenuineChern.symmetricAlgebraGen_comp_schemeSymAlgebraHom q
  have hq' : SheafOfModules.sheafifiedSymmetricGenerator (Opens.grothendieckTopology ↥X') E' ≫
      (symUnitalHom q').app 1 = q' ≫ γF' :=
    Stacks.Chow.GenuineChern.symmetricAlgebraGen_comp_schemeSymAlgebraHom q'
  let L := (Stacks.RelativeProj.symmetricSituationPullbackHom g E E' cE).comp (symUnitalHom q')
  let R := (baseAlgebraMapHom g (symUnitalHom q)).comp
    (Stacks.RelativeProj.symmetricSituationPullbackHom g F F' cF)
  have hL : (Scheme.Modules.pullback g).map γE ≫ L.app 1 = cE.inv ≫ q' ≫ γF' :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ (symUnitalHom q').app 1) hgenE).trans
        ((Category.assoc _ _ _).trans (congrArg (cE.inv ≫ ·) hq')))
  have hR : (Scheme.Modules.pullback g).map γE ≫ R.app 1 = cE.inv ≫ q' ≫ γF' :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ (Stacks.RelativeProj.symmetricSituationPullbackHom g F F' cF).app 1)
        (((Scheme.Modules.pullback g).map_comp _ _).symm.trans
          ((congrArg (Scheme.Modules.pullback g).map hq).trans
            ((Scheme.Modules.pullback g).map_comp _ _)))).trans
        ((Category.assoc _ _ _).trans
          ((congrArg ((Scheme.Modules.pullback g).map q ≫ ·) hgenF).trans
            ((Category.assoc _ _ _).symm.trans
              ((congrArg (· ≫ γF') hc'.symm).trans (Category.assoc _ _ _))))))
  exact hA.isUniversal.hom_ext (κ := cE.inv ≫ q' ≫ γF')
    (fun U s t => eq_of_heq (SheafOfModules.mul_comm_sheafifiedSymmetricAlgebra _ F' 1 1 U _ _))
    hL hR

/-- The degreewise form of `symmetricSituationPullbackHom_comp_symUnitalHom` on pulled-back
sections. -/
theorem symmetricSituationPullbackHom_symUnitalHom_pullbackSection
    (hc : q' ≫ cF.hom = cE.hom ≫ (Scheme.Modules.pullback g).map q) (n : ℤ)
    (W : X.Opens) (W' : X'.Opens) (h : W' ≤ g ⁻¹ᵁ W)
    (a : ((Scheme.Modules.symmetricAlgebra X E).piece n).val.obj (op W)) :
    ((symUnitalHom q').app n).val.app (op W')
        (((Stacks.RelativeProj.symmetricSituationPullbackHom g E E' cE).app n).val.app (op W')
          (Scheme.Modules.pullbackSection g ((Scheme.Modules.symmetricAlgebra X E).piece n) W W' h
            a)) =
      ((Stacks.RelativeProj.symmetricSituationPullbackHom g F F' cF).app n).val.app (op W')
        (Scheme.Modules.pullbackSection g ((Scheme.Modules.symmetricAlgebra X F).piece n) W W' h
          (((symUnitalHom q).app n).val.app (op W) a)) := by
  have key := congrArg (fun φ : UnitalHom _ _ => (φ.app n).val.app (op W')
    (Scheme.Modules.pullbackSection g ((Scheme.Modules.symmetricAlgebra X E).piece n) W W' h a))
    (symmetricSituationPullbackHom_comp_symUnitalHom g q q' cE cF hc)
  refine key.trans ?_
  change ((Stacks.RelativeProj.symmetricSituationPullbackHom g F F' cF).app n).val.app (op W')
      (((Scheme.Modules.pullback g).map ((symUnitalHom q).app n)).val.app (op W')
        (Scheme.Modules.pullbackSection g ((Scheme.Modules.symmetricAlgebra X E).piece n) W W' h
          a)) = _
  exact congrArg
    (fun z =>
      ((Stacks.RelativeProj.symmetricSituationPullbackHom g F F' cF).app n).val.app (op W') z)
    (Scheme.Modules.pullbackSection_naturality g ((symUnitalHom q).app n) W W' h a)

/-- **The two homomorphisms of graded rings of sections agree**: over affine opens `W' ⊆ g⁻¹W`,
the homomorphism `Γ(W, Sym ℰ) ⟶ Γ(W', Sym ℱ')` through `Γ(W', Sym ℰ')` equals the one through
`Γ(W, Sym ℱ)`. -/
theorem sectionHom_comp_baseChangeGradedHom
    (hc : q' ≫ cF.hom = cE.hom ≫ (Scheme.Modules.pullback g).map q)
    (hqcE : Stacks.SymGraded.IsQuasicoherentPieces E)
    (hqcF : Stacks.SymGraded.IsQuasicoherentPieces F)
    (hqcE' : Stacks.SymGraded.IsQuasicoherentPieces E')
    (hqcF' : Stacks.SymGraded.IsQuasicoherentPieces F')
    (W : X.AffineZariskiSite) (W' : X'.AffineZariskiSite) (h : W'.toOpens ≤ g ⁻¹ᵁ W.toOpens) :
    ((Stacks.SymGraded.schemeSheafGradedAlgebraHom q' hqcE' hqcF').sectionHom W'.toOpens).comp
        (Stacks.ProjectiveBundle.baseChangeGradedHom g E hqcE E' hqcE' cE W W' h) =
      (Stacks.ProjectiveBundle.baseChangeGradedHom g F hqcF F' hqcF' cF W W' h).comp
        ((Stacks.SymGraded.schemeSheafGradedAlgebraHom q hqcE hqcF).sectionHom W.toOpens) := by
  refine GradedRingHom.ext fun x => ?_
  induction x using DirectSum.induction_on with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | of n a =>
    change ((Stacks.SymGraded.schemeSheafGradedAlgebraHom q' hqcE' hqcF').sectionHom W'.toOpens)
        (Stacks.ProjectiveBundle.baseChangeGradedHom g E hqcE E' hqcE' cE W W' h
          (DirectSum.of _ n a)) =
      Stacks.ProjectiveBundle.baseChangeGradedHom g F hqcF F' hqcF' cF W W' h
        (((Stacks.SymGraded.schemeSheafGradedAlgebraHom q hqcE hqcF).sectionHom W.toOpens)
          (DirectSum.of _ n a))
    rw [Stacks.ProjectiveBundle.baseChangeGradedHom_of]
    refine (Stacks.AlgebraicGeometry.RelativeProjMapDomain.SheafGradedAlgebraHom.sectionHom_of
      (Stacks.SymGraded.schemeSheafGradedAlgebraHom q' hqcE' hqcF') W'.toOpens _).trans ?_
    refine Eq.trans ?_
      (congrArg (Stacks.ProjectiveBundle.baseChangeGradedHom g F hqcF F' hqcF' cF W W' h)
        (Stacks.AlgebraicGeometry.RelativeProjMapDomain.SheafGradedAlgebraHom.sectionHom_of
          (Stacks.SymGraded.schemeSheafGradedAlgebraHom q hqcE hqcF) W.toOpens a)).symm
    refine Eq.trans ?_ (Stacks.ProjectiveBundle.baseChangeGradedHom_of g F hqcF F' hqcF' cF W W' h n
      _).symm
    congr 1
    exact symmetricSituationPullbackHom_symUnitalHom_pullbackSection g q q' cE cF hc (n : ℤ)
      W.toOpens W'.toOpens h a
  | add x y hx hy =>
    exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)

end PullbackAlgebra

section Charts

variable {X : Scheme.{u}} {A : Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra X}

/-- **Morphisms out of a relative `Proj` are determined on a covering family of charts.** -/
theorem relativeProjData_hom_ext (P : Stacks.AlgebraicGeometry.RelativeProj.RelativeProjData A)
    {Y : Scheme.{u}} (f₁ f₂ : P.scheme ⟶ Y) {I : Type u} (W : I → X.AffineZariskiSite)
    (hcov : ∀ x : X, ∃ i, x ∈ (W i).toOpens)
    (h : ∀ i, P.chart (W i).toOpens (W i).2 ≫ f₁ = P.chart (W i).toOpens (W i).2 ≫ f₂) :
    f₁ = f₂ := by
  let 𝒰 : P.scheme.OpenCover :=
    Scheme.Cover.mkOfCovers I (fun i => AlgebraicGeometry.Proj (A.grading (W i).toOpens))
      (fun i => P.chart (W i).toOpens (W i).2) (fun x => by
        obtain ⟨i, hi⟩ := hcov (P.toBase x)
        obtain ⟨y, -, hy⟩ : x ∈ (P.chart (W i).toOpens (W i).2) ''ᵁ ⊤ := by
          rwa [Stacks.AlgebraicGeometry.RelativeProjTwistGlue.chart_image_top]
        exact ⟨i, y, hy⟩)
  exact 𝒰.hom_ext _ _ h

end Charts

/-- `Proj.map` along equal graded homomorphisms. -/
theorem proj_map_congr {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    [CommRing B] [SetLike τ B] [AddSubgroupClass τ B] {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜]
    [GradedRing ℬ] {f g : 𝒜 →+*ᵍ ℬ} (h : f = g)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (hg : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map g) :
    AlgebraicGeometry.Proj.map f hf = AlgebraicGeometry.Proj.map g hg := by
  subst h
  rfl

section Naturality

variable {X X' : Scheme.{u}} (g : X' ⟶ X) {E F : X.Modules}
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F]
  {E' F' : X'.Modules}
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E']
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F']
  (q : E ⟶ F) [Epi q] (q' : E' ⟶ F') [Epi q'] (cE : E' ≅ (Scheme.Modules.pullback g).obj E)
  (cF : F' ≅ (Scheme.Modules.pullback g).obj F)

/-- **The closed immersions of projective bundles commute with base change.** -/
theorem bundleEmbedding_comp_baseChangeHom
    (hc : q' ≫ cF.hom = cE.hom ≫ (Scheme.Modules.pullback g).map q) :
    Stacks.Chow.GenuineChern.bundleEmbedding q' ≫
        Stacks.ProjectiveBundle.baseChangeHom g E (Stacks.Chow.bundlePieces E) E'
          (Stacks.Chow.bundlePieces E') cE =
      Stacks.ProjectiveBundle.baseChangeHom g F (Stacks.Chow.bundlePieces F) F'
          (Stacks.Chow.bundlePieces F') cF ≫ Stacks.Chow.GenuineChern.bundleEmbedding q := by
  let I := {p : X.AffineZariskiSite × X'.AffineZariskiSite // p.2.toOpens ≤ g ⁻¹ᵁ p.1.toOpens}
  refine relativeProjData_hom_ext (Stacks.SymGraded.schemeProjectiveBundle F'
    (Stacks.Chow.bundlePieces F')) _ _ (I := I) (fun i => i.1.2) (fun x => ?_) (fun i => ?_)
  · obtain ⟨W, W', h, hx⟩ := Stacks.ProjectiveBundle.exists_affineZariskiSite_le_preimage g x
    exact ⟨⟨(W, W'), h⟩, hx⟩
  · obtain ⟨⟨W, W'⟩, h⟩ := i
    have hE := Stacks.ProjectiveBundle.chart_baseChangeHom g E (Stacks.Chow.bundlePieces E) E'
      (Stacks.Chow.bundlePieces E') cE W W' h
    have hF := Stacks.ProjectiveBundle.chart_baseChangeHom g F (Stacks.Chow.bundlePieces F) F'
      (Stacks.Chow.bundlePieces F') cF W W' h
    have hq' := Stacks.Chow.GenuineChern.chart_comp_bundleEmbedding q' W'.toOpens W'.2
    have hq := Stacks.Chow.GenuineChern.chart_comp_bundleEmbedding q W.toOpens W.2
    rw [Stacks.AlgebraicGeometry.ProjBundleSurjection.chartMap_eq_map] at hq hq'
    have hgr := sectionHom_comp_baseChangeGradedHom g q q' cE cF hc (Stacks.Chow.bundlePieces E)
      (Stacks.Chow.bundlePieces F) (Stacks.Chow.bundlePieces E') (Stacks.Chow.bundlePieces F') W W'
      h
    have hW' : IsAffineOpen W'.toOpens := W'.2
    have hW : IsAffineOpen W.toOpens := W.2
    have e5 : AlgebraicGeometry.Proj.map _
          (Stacks.AlgebraicGeometry.ProjBundleSurjection.irrelevant_le_map_sectionHom
            (Stacks.Chow.GenuineChern.surjectiveOnAffineSections_bundle q') hW') ≫
        AlgebraicGeometry.Proj.map _ (Stacks.ProjectiveBundle.irrelevant_le_baseChangeGradedHom g E
          (Stacks.Chow.bundlePieces E) E' (Stacks.Chow.bundlePieces E') cE W W' h) =
      AlgebraicGeometry.Proj.map _ (Stacks.ProjectiveBundle.irrelevant_le_baseChangeGradedHom g F
          (Stacks.Chow.bundlePieces F) F' (Stacks.Chow.bundlePieces F') cF W W' h) ≫
        AlgebraicGeometry.Proj.map _
          (Stacks.AlgebraicGeometry.ProjBundleSurjection.irrelevant_le_map_sectionHom
            (Stacks.Chow.GenuineChern.surjectiveOnAffineSections_bundle q) hW) :=
      (AlgebraicGeometry.Proj.map_comp _ _ _ _).symm.trans
        ((proj_map_congr hgr _ _).trans (AlgebraicGeometry.Proj.map_comp _ _ _ _))
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ Stacks.ProjectiveBundle.baseChangeHom g E (Stacks.Chow.bundlePieces E) E'
      (Stacks.Chow.bundlePieces E') cE) hq').trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (AlgebraicGeometry.Proj.map _ _ ≫ ·) hE).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ _) e5).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (AlgebraicGeometry.Proj.map _ _ ≫ ·) hq.symm).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ Stacks.Chow.GenuineChern.bundleEmbedding q) hF.symm).trans ?_
    exact Category.assoc _ _ _

end Naturality

end AlgebraicGeometry.Space.PrivateChern

end
