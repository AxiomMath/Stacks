module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianSchemeFirstCohomologyGenericPoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.EtaleLocalSection
public import StacksFrontier.AlgebraicGeometry.Size.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.FppfSectionOfLocallySurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.SmoothProductProjection
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.TorsorTotalSpaceAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.RepresentableByAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.Unconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedFppfCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothMorphismProperty
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.FirstCohomology.AbelianTorsor

/-!
# Torsors under a smooth commutative group scheme have sections étale locally

Let `G → W` be a smooth commutative group scheme and let `P` be an fppf torsor under the sheaf
of points of `G` on the big fppf site over `W`. Then every point of `W` has an affine étale
neighbourhood over which `P` has a section.

## Main definitions

* `Stacks.Cohomology.Torsors.prodYonedaIsoOfSection`: a section `s` of a torsor `F` under an
  abelian sheaf `H` over an object `U` identifies `h_U × H` with `h_U × F`.
* `AlgebraicGeometry.pointsSheafYonedaIso`: the underlying presheaf of sets of the sheaf of
  points of `G` is represented by `G`.

## Main results

* `AlgebraicGeometry.isAlgebraicSpace_torsor_pointsSheaf`: the torsor `P` is an algebraic space
  over `W`.
* `AlgebraicGeometry.isSmooth_torsor_pointsSheaf`: the structure morphism of `P` is smooth when
  `G → W` is.
* `AlgebraicGeometry.exists_etale_section_of_torsor`: `P` has a section over an affine étale
  neighbourhood of every point of `W`.

## Implementation notes

A torsor is locally surjective onto the terminal sheaf, so it has a section `s` over a single
object `V` of the site whose structure morphism `V → W` is flat, locally of finite presentation
and surjective (`AlgebraicGeometry.Space.exists_fppf_section`). The section identifies
`h_V × P` with `h_V × G`, which is an algebraic space smooth over `h_V`. So `P` is an algebraic
space by the bootstrap theorem (Stacks 04S6, condition (3)), and its structure morphism is
smooth by fpqc locality on the base (Stacks 0429). An étale atlas `U₀ → P` then makes `U₀ → W`
a smooth morphism of schemes, surjective onto `W` because `P → W` is: a point of `V` lifts to
the atlas along `s`. A smooth morphism has étale local sections through every point of its
image (Stacks 055U), and an affine open of the étale neighbourhood is small enough to lie in
the site, because it is quasi-compact and locally of finite type over `W` (Stacks 04T7).

This is the argument of Stacks 0AFA, which works over a field, carried out over an arbitrary
base: there the trivialising object is any member of a covering, here it is the single object
given by local surjectivity.

## References

* [Stacks Project, Tag 0AFA](https://stacks.math.columbia.edu/tag/0AFA)
* [Stacks Project, Tag 055U](https://stacks.math.columbia.edu/tag/055U)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u

namespace Stacks.Cohomology.Torsors

/-- A section `s` of a torsor `F` under an abelian sheaf `H` over an object `U` identifies
`h_U × H` with `h_U × F`: a pair `(f, g)` goes to `(f, g · f^* s)`, and the inverse sends
`(f, t)` to `(f, t - f^* s)`. -/
def prodYonedaIsoOfSection {C : Type*} [Category C] {J : GrothendieckTopology C}
    (H : Sheaf J AddCommGrpCat.{u}) (F : AbelianTorsor H)
    (U : C) (s : F.1.presheaf.obj (op U)) :
    yoneda.obj U ⨯ (H.obj ⋙ forget AddCommGrpCat) ≅ yoneda.obj U ⨯ F.1.presheaf := by
  let A := yoneda.obj U ⨯ (H.obj ⋙ forget AddCommGrpCat)
  let P := yoneda.obj U ⨯ F.1.presheaf
  let a : A ⟶ F.1.presheaf :=
    { app := fun V => ↾fun t => F.1.act V
        (Multiplicative.ofAdd ((prod.snd : A ⟶ _).app V t))
        (F.1.presheaf.map ((prod.fst : A ⟶ _).app V t).op s)
      naturality := by
        intro V W f
        ext t
        change F.1.act W
          (Multiplicative.ofAdd ((prod.snd : A ⟶ _).app W (A.map f t)))
          (F.1.presheaf.map ((prod.fst : A ⟶ _).app W (A.map f t)).op s) =
          F.1.presheaf.map f (F.1.act V
            (Multiplicative.ofAdd ((prod.snd : A ⟶ _).app V t))
            (F.1.presheaf.map ((prod.fst : A ⟶ _).app V t).op s))
        refine Eq.trans ?_ (F.1.naturality f _ _).symm
        rw [NatTrans.naturality_apply (prod.snd : A ⟶ _)]
        rw [NatTrans.naturality_apply (prod.fst : A ⟶ _)]
        congr 1
        change F.1.presheaf.map
          (f.unop ≫ (prod.fst : A ⟶ _).app V t).op s = _
        rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
        rfl }
  let d : P ⟶ H.obj ⋙ forget AddCommGrpCat :=
    { app := fun V => ↾fun t => torsorDifference H F V
        ((prod.snd : P ⟶ _).app V t)
        (F.1.presheaf.map ((prod.fst : P ⟶ _).app V t).op s)
      naturality := by
        intro V W f
        ext t
        change torsorDifference H F W
          ((prod.snd : P ⟶ _).app W (P.map f t))
          (F.1.presheaf.map ((prod.fst : P ⟶ _).app W (P.map f t)).op s) =
          H.obj.map f (torsorDifference H F V
            ((prod.snd : P ⟶ _).app V t)
            (F.1.presheaf.map ((prod.fst : P ⟶ _).app V t).op s))
        rw [torsorDifference_naturality H F]
        rw [NatTrans.naturality_apply (prod.snd : P ⟶ _)]
        rw [NatTrans.naturality_apply (prod.fst : P ⟶ _)]
        congr 1
        change F.1.presheaf.map
          (f.unop ≫ (prod.fst : P ⟶ _).app V t).op s = _
        rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
        rfl }
  refine ⟨prod.lift prod.fst a, prod.lift prod.fst d, ?_, ?_⟩
  · apply prod.hom_ext
    · simp
    · simp only [Category.assoc, prod.lift_snd, Category.id_comp]
      ext V t
      change torsorDifference H F V
        ((prod.snd : P ⟶ _).app V ((prod.lift prod.fst a).app V t))
        (F.1.presheaf.map
          ((prod.fst : P ⟶ _).app V ((prod.lift prod.fst a).app V t)).op s) = _
      have hfst := ConcreteCategory.congr_hom
        (NatTrans.congr_app (prod.lift_fst (prod.fst : A ⟶ _) a) V) t
      have hsnd := ConcreteCategory.congr_hom
        (NatTrans.congr_app (prod.lift_snd (prod.fst : A ⟶ _) a) V) t
      change (prod.fst : P ⟶ _).app V ((prod.lift prod.fst a).app V t) = _ at hfst
      change (prod.snd : P ⟶ _).app V ((prod.lift prod.fst a).app V t) = _ at hsnd
      rw [hfst, hsnd]
      exact torsorDifference_eq_of_act H F V _ _ _ rfl
  · apply prod.hom_ext
    · simp
    · simp only [Category.assoc, prod.lift_snd, Category.id_comp]
      ext V t
      change F.1.act V
        (Multiplicative.ofAdd ((prod.snd : A ⟶ _).app V ((prod.lift prod.fst d).app V t)))
        (F.1.presheaf.map
          ((prod.fst : A ⟶ _).app V ((prod.lift prod.fst d).app V t)).op s) = _
      have hfst := ConcreteCategory.congr_hom
        (NatTrans.congr_app (prod.lift_fst (prod.fst : P ⟶ _) d) V) t
      have hsnd := ConcreteCategory.congr_hom
        (NatTrans.congr_app (prod.lift_snd (prod.fst : P ⟶ _) d) V) t
      change (prod.fst : A ⟶ _).app V ((prod.lift prod.fst d).app V t) = _ at hfst
      change (prod.snd : A ⟶ _).app V ((prod.lift prod.fst d).app V t) = _ at hsnd
      rw [hfst, hsnd]
      exact torsorDifference_act H F V _ _

/-- The isomorphism `prodYonedaIsoOfSection` commutes with the projections to `h_U`. -/
@[reassoc (attr := simp)]
theorem prodYonedaIsoOfSection_hom_fst {C : Type*} [Category C] {J : GrothendieckTopology C}
    (H : Sheaf J AddCommGrpCat.{u}) (F : AbelianTorsor H)
    (U : C) (s : F.1.presheaf.obj (op U)) :
    (prodYonedaIsoOfSection H F U s).hom ≫ prod.fst = prod.fst :=
  prod.lift_fst _ _

end Stacks.Cohomology.Torsors

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (W : Scheme.{u}) (hW : B.Contains W)

/-- The underlying presheaf of sets of the sheaf of points of a commutative group scheme `G`
over `W` is represented by `G`, as an object of the big fppf site over `W`. -/
def pointsSheafYonedaIso (G : Over W) [GrpObj G] [IsCommMonObj G] (hG : B.Contains G.left) :
    yoneda.obj (groupSchemeObj B W hW G hG) ≅
      (pointsSheaf B W hW G hG).obj ⋙ forget AddCommGrpCat.{u} :=
  have e₁ : yoneda.obj (groupSchemeObj B W hW G hG) ≅
      (Over.post (X := B.obj hW) B.inclusion).op ⋙ yoneda.obj G :=
    NatIso.ofComponents (fun Z => Equiv.toIso
      ((Functor.FullyFaithful.ofFullyFaithful
        (Over.post (X := B.obj hW) B.inclusion)).homEquiv)) (by
      intro Z Z' φ
      ext g
      exact (Over.post (X := B.obj hW) B.inclusion).map_comp φ.unop g)
  have e₂ : (Over.post (X := B.obj hW) B.inclusion).op ⋙ yoneda.obj G ≅
      pointsPresheaf B W hW G ⋙ forget AddCommGrpCat.{u} :=
    NatIso.ofComponents (fun _ => Iso.refl _) (by intro Z Z' φ; ext g; rfl)
  e₁ ≪≫ e₂

/-- The sheaf of points of a commutative group scheme over `W`, as a presheaf of sets, is an
algebraic space over `W`: it is represented by `G`. -/
theorem isAlgebraicSpace_pointsSheaf (G : Over W) [GrpObj G] [IsCommMonObj G]
    (hG : B.Contains G.left) :
    IsAlgebraicSpace B W hW ((pointsSheaf B W hW G hG).obj ⋙ forget AddCommGrpCat.{u}) :=
  Space.isAlgebraicSpace_of_iso B W hW (pointsSheafYonedaIso B W hW G hG)
    (isAlgebraicSpace_yoneda B W hW _)

/-- A torsor under the sheaf of points of `G` is locally surjective onto the terminal sheaf of
the big fppf site over `W`: it has sections locally. -/
theorem isLocallySurjective_torsor_pointsSheaf (G : Over W) [GrpObj G] [IsCommMonObj G]
    (hG : B.Contains G.left)
    (F : Stacks.Cohomology.Torsors.AbelianTorsor (pointsSheaf B W hW G hG)) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology B W hW)
      ((Space.isTerminal_yoneda_obj_base B W hW).from F.1.presheaf) := by
  constructor
  intro U s
  obtain ⟨S, hS, hne⟩ := F.2 U
  refine (BigFppfOver.topology B W hW).superset_covering ?_ hS
  intro V f hf
  obtain ⟨x⟩ := hne hf
  exact ⟨x, Over.mkIdTerminal.hom_ext _ _⟩

/-- A torsor under the sheaf of points of `G` has a section over a single object of the big
fppf site over `W` whose structure morphism is flat, locally of finite presentation and
surjective. -/
theorem exists_fppf_section_torsor_pointsSheaf (G : Over W) [GrpObj G] [IsCommMonObj G]
    (hG : B.Contains G.left)
    (F : Stacks.Cohomology.Torsors.AbelianTorsor (pointsSheaf B W hW G hG)) :
    ∃ (V : BigFppfOver B W hW) (k : V ⟶ Over.mk (𝟙 (B.obj hW)))
      (_ : F.1.presheaf.obj (op V)),
      Flat ((BigFppfOver.toScheme B W hW).map k) ∧
      LocallyOfFinitePresentation ((BigFppfOver.toScheme B W hW).map k) ∧
      Surjective ((BigFppfOver.toScheme B W hW).map k) := by
  obtain ⟨V, k, s, -, hfl, hlfp, hsurj⟩ := Space.exists_fppf_section F.1.isSheaf
    ((Space.isTerminal_yoneda_obj_base B W hW).from F.1.presheaf)
    (isLocallySurjective_torsor_pointsSheaf B W hW G hG F)
  exact ⟨V, k, yonedaEquiv s, hfl, hlfp, hsurj⟩

/-- **A torsor under the sheaf of points of a commutative group scheme is an algebraic space.**
After the flat, locally finitely presented, surjective base change along an object `V` of the
site over which it has a section, it becomes `h_V × G`, which is an algebraic space; so it is
one by the bootstrap theorem, Stacks 04S6, condition (3). -/
theorem isAlgebraicSpace_torsor_pointsSheaf (G : Over W) [GrpObj G] [IsCommMonObj G]
    (hG : B.Contains G.left)
    (F : Stacks.Cohomology.Torsors.AbelianTorsor (pointsSheaf B W hW G hG)) :
    IsAlgebraicSpace B W hW F.1.presheaf := by
  obtain ⟨V, k, s, hfl, hlfp, hsurj⟩ := exists_fppf_section_torsor_pointsSheaf B W hW G hG F
  let ht := Space.isTerminal_yoneda_obj_base B W hW
  have hZ : IsAlgebraicSpace B W hW (yoneda.obj V ⨯ F.1.presheaf) :=
    Space.isAlgebraicSpace_of_iso B W hW
      (Stacks.Cohomology.Torsors.prodYonedaIsoOfSection _ F V s)
      (isAlgebraicSpace_prod B W hW (isAlgebraicSpace_yoneda B W hW V)
        (isAlgebraicSpace_pointsSheaf B W hW G hG))
  have hsq : IsPullback (prod.snd : yoneda.obj V ⨯ F.1.presheaf ⟶ F.1.presheaf) prod.fst
      (ht.from F.1.presheaf) (yoneda.map k) := by
    rw [ht.hom_ext (yoneda.map k) (ht.from _)]
    exact (ht.isPullback_prod (yoneda.obj V) F.1.presheaf).flip
  exact Space.isAlgebraicSpace_of_section_cover
    (Space.isBootstrapAlgebraicSpaceAlongFlatSurjection B W hW) k hsq F.1.isSheaf hZ
    hfl hlfp hsurj

/-- **A torsor under the sheaf of points of a smooth commutative group scheme is smooth over the
base.** After the fppf base change along an object `V` over which it has a section it becomes
the projection `h_V × G → h_V`, which is smooth; smoothness is fpqc local on the base
(Stacks 0429). -/
theorem isSmooth_torsor_pointsSheaf (G : Over W) [GrpObj G] [IsCommMonObj G] [Smooth G.hom]
    (hG : B.Contains G.left)
    (F : Stacks.Cohomology.Torsors.AbelianTorsor (pointsSheaf B W hW G hG)) :
    Space.IsSmooth B W hW ((Space.isTerminal_yoneda_obj_base B W hW).from F.1.presheaf) := by
  obtain ⟨V, k, s, hfl, hlfp, hsurj⟩ := exists_fppf_section_torsor_pointsSheaf B W hW G hG F
  let ht := Space.isTerminal_yoneda_obj_base B W hW
  let T : BigFppfOver B W hW := Over.mk (𝟙 (B.obj hW))
  have hF := isAlgebraicSpace_torsor_pointsSheaf B W hW G hG F
  have hGa := isAlgebraicSpace_pointsSheaf B W hW G hG
  let Gp := (pointsSheaf B W hW G hG).obj ⋙ forget AddCommGrpCat.{u}
  let Tsp : AlgebraicSpaces B W hW := ⟨yoneda.obj T, isAlgebraicSpace_yoneda B W hW T⟩
  let Vsp : AlgebraicSpaces B W hW := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B W hW V⟩
  let Fsp : AlgebraicSpaces B W hW := ⟨F.1.presheaf, hF⟩
  let f : Fsp ⟶ Tsp := ObjectProperty.homMk (ht.from _)
  let q : Vsp ⟶ Tsp := ObjectProperty.homMk (yoneda.map k)
  let P := Space.smoothMorphismProperty B W hW
  have : P.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hcov : Space.IsFpqcCovering B W hW (fun _ : PUnit.{u + 2} => q.hom) :=
    Space.isFpqcCovering_of_isFppfCovering B W hW _ _
      (Space.isFppfCovering_yoneda_map B W hW (fun _ : PUnit.{u + 2} => V) (fun _ => k)
        (fun _ => hfl) (fun _ => hlfp) (fun x => ⟨PUnit.unit, hsurj.1 x⟩))
  -- the base change of the torsor along `V` is `h_V × G`
  let hPF := isAlgebraicSpace_prod B W hW Vsp.property hF
  let PF : AlgebraicSpaces B W hW := ⟨Vsp.obj ⨯ Fsp.obj, hPF⟩
  let qF : PF ⟶ Vsp := ObjectProperty.homMk prod.fst
  let pF : PF ⟶ Fsp := ObjectProperty.homMk prod.snd
  have hpbF : IsPullback pF qF f q := by
    refine IsPullback.of_map (ObjectProperty.ι _) ?_ ?_
    · apply ObjectProperty.hom_ext
      exact ht.hom_ext _ _
    · change IsPullback (prod.snd : yoneda.obj V ⨯ F.1.presheaf ⟶ F.1.presheaf) prod.fst
        (ht.from F.1.presheaf) (yoneda.map k)
      rw [ht.hom_ext (yoneda.map k) (ht.from _)]
      exact (ht.isPullback_prod (yoneda.obj V) F.1.presheaf).flip
  have hsmG : Smooth ((BigFppfOver.toScheme B W hW).map
      (Over.mkIdTerminal.from (groupSchemeObj B W hW G hG))) := by
    change Smooth (B.inclusion.map (Over.mkIdTerminal.from (groupSchemeObj B W hW G hG)).left)
    rw [Over.mkIdTerminal_from_left]
    exact (inferInstance : Smooth G.hom)
  have hqG : Space.IsSmooth B W hW (prod.fst : yoneda.obj V ⨯ Gp ⟶ yoneda.obj V) :=
    Space.isSmooth_prod_fst_of_representableBy B W hW (yoneda.obj V) Gp Vsp.property
      (Functor.representableByEquiv.symm (pointsSheafYonedaIso B W hW G hG))
      (Space.isSmooth_yoneda_map_mkIdTerminal_from B W hW _ hsmG)
  let PG : AlgebraicSpaces B W hW :=
    ⟨yoneda.obj V ⨯ Gp, isAlgebraicSpace_prod B W hW Vsp.property hGa⟩
  let e : PG ≅ PF := ObjectProperty.isoMk _
    (Stacks.Cohomology.Torsors.prodYonedaIsoOfSection _ F V s)
  have he : e.hom ≫ qF = (ObjectProperty.homMk prod.fst : PG ⟶ Vsp) := by
    apply ObjectProperty.hom_ext
    exact Stacks.Cohomology.Torsors.prodYonedaIsoOfSection_hom_fst _ F V s
  have hqF : P qF := by
    apply (MorphismProperty.cancel_left_of_respectsIso P e.hom qF).mp
    rw [he]
    exact hqG
  have hf : P f := by
    apply MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd
      (P := P)
      (K := Space.Topology.precoverage.{u, u + 1} .fpqc B W hW)
      (R := Presieve.ofArrows (fun _ : PUnit.{u + 2} => Vsp) (fun _ => q))
      ⟨_, _, _, rfl, Tsp.property, (fun _ => Vsp.property), hcov⟩
    rintro _ _ _ ⟨i⟩
    have hh : P (hpbF.isoPullback.inv ≫ qF) :=
      MorphismProperty.RespectsIso.precomp P hpbF.isoPullback.inv qF hqF
    rwa [hpbF.isoPullback_inv_snd] at hh
  exact hf

/-- **An fppf torsor under a smooth commutative group scheme is trivial étale locally.** Let
`G → W` be a smooth commutative group scheme and `F` a torsor under the sheaf of points of `G`
on the big fppf site over `W`. Then every point `w` of `W` is the image of a point `u` of an
affine object `U` of the site, étale over `W`, over which `F` has a section.

The torsor is an algebraic space smooth over `W`, so an étale atlas `U₀ → F` is a smooth
morphism of schemes `U₀ → W`, surjective because `F → W` is; Stacks 055U gives an étale
neighbourhood of `w` mapping to `U₀` over `W`, and an affine open of it through the point over
`w` lies in the site. -/
theorem exists_etale_section_of_torsor (G : Over W) [GrpObj G] [IsCommMonObj G] [Smooth G.hom]
    (hG : B.Contains G.left)
    (F : Stacks.Cohomology.Torsors.AbelianTorsor (pointsSheaf B W hW G hG)) (w : W) :
    ∃ (U : BigFppfOver B W hW) (u : U.left.obj), Etale (B.inclusion.map U.hom) ∧
      IsAffine U.left.obj ∧ (B.inclusion.map U.hom).base u = w ∧
      Nonempty (F.1.presheaf.obj (op U)) := by
  classical
  let ht := Space.isTerminal_yoneda_obj_base B W hW
  let T : BigFppfOver B W hW := Over.mk (𝟙 (B.obj hW))
  let Ts := BigFppfOver.toScheme B W hW
  have hF := isAlgebraicSpace_torsor_pointsSheaf B W hW G hG F
  have hsmt := isSmooth_torsor_pointsSheaf B W hW G hG F
  obtain ⟨V, k, s, -, -, hsurj⟩ := exists_fppf_section_torsor_pointsSheaf B W hW G hG F
  -- an étale atlas of the torsor, smooth over `W`
  obtain ⟨U₀, a, hasurj, haet⟩ := hF.exists_atlas
  have hsm : Space.IsSmooth B W hW (a ≫ ht.from F.1.presheaf) :=
    Space.isSmooth_comp B W hW (isAlgebraicSpace_yoneda B W hW U₀) hF
      (isAlgebraicSpace_yoneda B W hW T) a _
      (Space.isSmooth_of_isEtale B W hW hF ((Space.isEtale_iff_presheaf_of_yoneda B W hW a).2 haet))
      hsmt
  let h₀ : U₀ ⟶ T := Over.mkIdTerminal.from U₀
  have hh : yoneda.map h₀ = a ≫ ht.from F.1.presheaf := ht.hom_ext _ _
  have hU₀ : Smooth (Ts.map h₀) :=
    (Space.holdsOnEveryEtaleChart_yoneda_map_iff B W hW Smooth.isEtaleLocalOnSourceAndTarget
      h₀).1 (hh ▸ hsm)
  -- the atlas has a point over `w`
  obtain ⟨v, hv⟩ := hsurj.1 w
  let snd := hasurj.rep.snd (yonedaEquiv.symm s)
  obtain ⟨y, hy⟩ := (show Surjective (Ts.map snd) from
    hasurj.property_snd (yonedaEquiv.symm s)).1 v
  let m := hasurj.rep.fst' (yonedaEquiv.symm s)
  have hmh : m ≫ h₀ = snd ≫ k := Over.mkIdTerminal.hom_ext _ _
  have hu₀ : (Ts.map h₀).base ((Ts.map m).base y) = w := by
    rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, hmh, Functor.map_comp,
      Scheme.Hom.comp_apply, hy, hv]
  -- an étale neighbourhood of `w` lifting to the atlas, Stacks 055U
  obtain ⟨N, g, hg⟩ := exists_etaleNeighborhood_lift_of_smooth (Ts.map h₀) w
    ⟨(Ts.map m).base y, hu₀⟩
  obtain ⟨O, hO, hmem, -⟩ := exists_isAffineOpen_mem_and_subset
    (X := N.scheme) (x := N.point) (U := ⊤) trivial
  have : IsAffine O.toScheme := hO
  let e : O.toScheme ⟶ W := O.ι ≫ N.toBase
  have : Etale e := inferInstance
  have hsize : B.Contains O.toScheme :=
    lt_of_le_of_lt (Scheme.size_le_of_locallyOfFiniteType e) hW
  let U : BigFppfOver B W hW := Over.mk (ObjectProperty.homMk e : B.obj hsize ⟶ B.obj hW)
  have hTs : Ts.map h₀ = B.inclusion.map U₀.hom := by
    change B.inclusion.map (Over.mkIdTerminal.from U₀).left = _
    rw [Over.mkIdTerminal_from_left]
  let j : U ⟶ U₀ := Over.homMk (ObjectProperty.homMk (O.ι ≫ g)) (by
    apply B.inclusion.map_injective
    change (O.ι ≫ g) ≫ B.inclusion.map U₀.hom = O.ι ≫ N.toBase
    rw [Category.assoc, ← hTs, hg])
  obtain ⟨u, hu⟩ : N.point ∈ Set.range O.ι := by rw [Scheme.Opens.range_ι]; exact hmem
  refine ⟨U, u, this, hO, ?_, ⟨F.1.presheaf.map j.op (yonedaEquiv a)⟩⟩
  change (O.ι ≫ N.toBase) u = w
  rw [Scheme.Hom.comp_apply, hu]
  exact N.map_point

end AlgebraicGeometry

end
