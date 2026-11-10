module

public import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
public import StacksFrontier.AlgebraicGeometry.ProEtale.AppProetaleCover
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.Characterization
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.IndEtale
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndEtaleConstruction.WeaklyEtaleIndEtaleExtension
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.AffineDense
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.AffineIndEtale
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.AffineIndEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.WContractibleCoverCardinality
public import StacksFrontier.RingTheory.Etale.IndEtaleUniverse
public import StacksCore.Tactic.StacksAttribute

/-!
# The affine ind-étale site is a dense subsite

For an affine scheme `S` in a big pro-étale site, every affine object of the small pro-étale
site of `S` is covered by a single affine ind-étale one: the ring of global sections is weakly
étale over that of `S`, hence admits a faithfully flat ind-étale extension, and the extension
can be chosen small enough to stay inside the big site. The affine ind-étale objects are
therefore cover-dense in the small pro-étale site, the topology they carry is the induced one,
and restriction of sheaves along the inclusion is an equivalence of topoi.

## Main results

* `AlgebraicGeometry.ProEtale.AffineIndEtaleProetale.inclusion_isCoverDense`: the affine
  ind-étale objects are cover-dense in the small pro-étale site.
* `AlgebraicGeometry.ProEtale.AffineIndEtaleProetale.inclusion_isContinuous`: restriction along
  the inclusion takes pro-étale sheaves to sheaves on the affine ind-étale site.
* `AlgebraicGeometry.ProEtale.AffineIndEtaleProetale.isEquivalence_restriction`: that restriction
  is an equivalence of categories of sheaves of sets.

## Implementation notes

The topology of the affine ind-étale site is shown to be the topology induced from the small
pro-étale site, `AlgebraicGeometry.ProEtale.AffineIndEtaleProetale.topology_eq_restricted`; this
is what turns cover density into the dense-subsite property and hence into the equivalence of
topoi.
The inequality that needs work is that an induced covering sieve already contains a standard
pro-étale covering family, which is proved by induction over the saturation of the small-site
precoverage.

Smallness of the ind-étale extension is where the cardinal bound of the big pro-étale site is
used: the extension of Stacks 0984 is bounded by `Cardinal.proetaleBound` of the size of the
object being covered, and the big site is closed under that bound.

The sheaf values are taken in `Type (max (u + 1) v)` so that the structured-arrow limits in the
dense-subsite comparison theorem exist; the affine ind-étale site is essentially small at that
universe by `AlgebraicGeometry.ProEtale.AffineIndEtaleProetale.essentiallySmall`.

## References

* [Stacks Project, Tag 098X](https://stacks.math.columbia.edu/tag/098X)
-/

@[expose] public section

open CategoryTheory Opposite
open scoped AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.ProEtale

/-- A weakly étale ring map has a faithfully flat ind-étale extension of its target after which
the composite is ind-étale, with the extension bounded by `Cardinal.proetaleBound κ` whenever
`κ` is an infinite bound for the target. -/
private theorem exists_bounded_faithfullyFlat_indEtale_extension {A D : Type u} [CommRing A]
    [CommRing D] (f : A →+* D) (hf : letI := f.toAlgebra; Algebra.WeaklyEtale A D)
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ) (hD : Cardinal.mk D ≤ κ) :
    ∃ (E : Type u) (_ : CommRing E) (g : D →+* E),
      g.FaithfullyFlat ∧
        ObjectProperty.ind.{u} (fun C : Under (CommRingCat.of D) ↦ C.hom.hom.Etale)
          (Under.mk (CommRingCat.ofHom g)) ∧
        ObjectProperty.ind.{u} (fun C : Under (CommRingCat.of A) ↦ C.hom.hom.Etale)
          (Under.mk (CommRingCat.ofHom (g.comp f))) ∧
        Cardinal.mk E ≤ Cardinal.proetaleBound κ := by
  obtain ⟨E, hE, g, hff, hindDE, hwE, hsize⟩ :=
    exists_small_faithfullyFlat_ind_etale_wContractible D κ hκ hD
  let _ : Algebra D E := g.toAlgebra
  let _ : Algebra A D := f.toAlgebra
  let _ : Algebra A E := (g.comp f).toAlgebra
  let _ : IsScalarTower A D E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hweakDE : Algebra.WeaklyEtale D E :=
    Algebra.weaklyEtale_of_ind_etale (indEtale_iff_ind_etale_underMk.2 hindDE)
  have hweakAE : Algebra.WeaklyEtale A E := Algebra.WeaklyEtale.trans A D E
  obtain ⟨E', hE', e, heff, hindEE', hindAE'⟩ :=
    exists_faithfullyFlat_indEtale_extension (g.comp f) hweakAE
  let _ : Algebra E E' := e.toAlgebra
  let _ : Algebra A E' := (e.comp (g.comp f)).toAlgebra
  let _ : IsScalarTower A E E' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hweakEE : Algebra.WeaklyEtale E E' :=
    Algebra.weaklyEtale_of_ind_etale (indEtale_iff_ind_etale_underMk.2 hindEE')
  obtain ⟨r⟩ := hwE E' (Algebra.weaklyEtale_iff E E' |>.mp hweakEE) heff
  have hRetract : r.toRingHom.comp e = RingHom.id E := by
    ext x
    exact r.commutes x
  refine ⟨E, hE, g, hff, hindDE, ?_, hsize.trans (le_max_left _ _)⟩
  refine (MorphismProperty.ind_iff_ind_underMk (CommRingCat.ofHom (g.comp f))).1
    (indEtale_of_isSplitEpiFactorization (CommRingCat.ofHom (g.comp f))
      (CommRingCat.ofHom (e.comp (g.comp f))) (CommRingCat.ofHom e)
      (CommRingCat.ofHom r.toRingHom) ?_ ?_ ?_)
  · change CommRingCat.ofHom (e.comp (g.comp f)) =
      CommRingCat.ofHom (g.comp f) ≫ CommRingCat.ofHom e
    rfl
  · change CommRingCat.ofHom (r.toRingHom.comp e) = CommRingCat.ofHom (RingHom.id E)
    rw [hRetract]
  · exact (MorphismProperty.ind_iff_ind_underMk
      (CommRingCat.ofHom (e.comp (g.comp f)))).2 hindAE'

variable (B : BigProetaleSite.{u}) (S : B.Scheme)

namespace AffineIndEtaleProetale

/-- Every affine object of the small pro-étale site of an affine `S` is covered by a single
affine ind-étale object. -/
private theorem exists_cover_affine [IsAffine S.obj]
    (X : SmallProetale B S.obj S.property) (hX : IsAffine (B.inclusion.obj X.obj.left)) :
    ∃ (V : AffineIndEtaleProetale B S) (f : (inclusion B S).obj V ⟶ X),
      SmallProetale.IsCovering B S.obj S.property
        ⟨X, PreZeroHypercover.singleton.{u + 1} f⟩ ∧
      Sieve.generate (Presieve.singleton f) ∈
        SmallProetale.topology B S.obj S.property X := by
  classical
  let U := B.inclusion.obj X.obj.left
  let fX : U ⟶ S.obj := B.inclusion.map X.obj.hom
  let A := Γ(S.obj, ⊤)
  let D := Γ(U, ⊤)
  let fr : A →+* D := fX.appTop.hom
  have hfr : let := fr.toAlgebra; Algebra.WeaklyEtale A D :=
    @weaklyEtale_appTop_of_isAffine _ _ _ _ fX X.property
  have hκ : Cardinal.aleph0 ≤ U.size := by
    rw [Scheme.size_of_isAffine U]
    exact le_max_left _ _
  have hD : Cardinal.mk D ≤ U.size := by
    rw [Scheme.size_of_isAffine U]
    exact le_max_right _ _
  obtain ⟨E, hE, g, hff, hindDE, hindAE, hsize⟩ :=
    exists_bounded_faithfullyFlat_indEtale_extension fr hfr U.size hκ hD
  let _ : Algebra D E := g.toAlgebra
  let _ : Algebra A D := fr.toAlgebra
  let _ : Algebra A E := (g.comp fr).toAlgebra
  let φ : CommRingCat.of A ⟶ CommRingCat.of E := CommRingCat.ofHom (g.comp fr)
  let P : Scheme := Scheme.Spec.obj (op (CommRingCat.of E))
  let q : P ⟶ U := Scheme.Spec.map (CommRingCat.ofHom g).op ≫ U.isoSpec.inv
  let p : P ⟶ S.obj := q ≫ fX
  have hκbound : Cardinal.aleph0 ≤ Cardinal.proetaleBound U.size := by
    have hbound : U.size ^ Cardinal.aleph0 ≤ Cardinal.proetaleBound U.size := by
      change U.size ^ Cardinal.aleph0 ≤
        max (U.size ^ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ U.size))))
          (max (U.size ^ Cardinal.aleph0) (Order.succ U.size))
      exact (le_max_left _ _).trans (le_max_right _ _)
    exact hκ.trans ((Cardinal.self_le_power U.size Cardinal.one_le_aleph0).trans hbound)
  have hPsize : P.size ≤ Cardinal.proetaleBound U.size := by
    have hspec : P.size = max Cardinal.aleph0 (Cardinal.mk E) := by
      simpa [P] using Scheme.size_Spec (CommRingCat.of E)
    rw [hspec]
    exact max_le hκbound hsize
  have hPcut : P.size < B.cutoff := B.closed_under_proetaleBound X.obj.left.property hPsize
  let YB : B.Scheme := ⟨P, hPcut⟩
  let qB : YB ⟶ X.obj.left :=
    B.inclusion.preimage (show B.inclusion.obj YB ⟶ B.inclusion.obj X.obj.left from q)
  have hqB : B.inclusion.map qB = q :=
    B.inclusion.map_preimage (show B.inclusion.obj YB ⟶ B.inclusion.obj X.obj.left from q)
  let pB : YB ⟶ (⟨S.obj, S.property⟩ : B.Scheme) :=
    B.inclusion.preimage
      (show B.inclusion.obj YB ⟶ B.inclusion.obj (⟨S.obj, S.property⟩ : B.Scheme) from p)
  have hpB : B.inclusion.map pB = p :=
    B.inclusion.map_preimage
      (show B.inclusion.obj YB ⟶ B.inclusion.obj (⟨S.obj, S.property⟩ : B.Scheme) from p)
  have hindP : ObjectProperty.ind.{u}
      (fun C : Under (CommRingCat.of A) ↦ C.hom.hom.Etale) (Under.mk p.appTop) := by
    let e := (Scheme.ΓSpecIso (CommRingCat.of E)).commRingCatIsoToRingEquiv
    have heq : p.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of E)).hom = φ := by
      change (fX.appTop ≫ q.appTop) ≫ (Scheme.ΓSpecIso (CommRingCat.of E)).hom = φ
      have hinv : U.isoSpec.inv.appTop = (Scheme.ΓSpecIso D).inv := by
        apply (cancel_mono (Scheme.ΓSpecIso D).hom).1
        have hh : U.isoSpec.hom.appTop = (Scheme.ΓSpecIso D).hom := Scheme.toSpecΓ_appTop U
        rw [Iso.inv_hom_id, ← hh, ← Scheme.Hom.comp_appTop, U.isoSpec.hom_inv_id]
        rfl
      have hqmap : q.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of E)).hom =
          CommRingCat.ofHom g := by
        change (U.isoSpec.inv.appTop ≫ (Scheme.Spec.map (CommRingCat.ofHom g).op).appTop) ≫
          (Scheme.ΓSpecIso (CommRingCat.of E)).hom = CommRingCat.ofHom g
        rw [hinv]
        have hnat := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom g)
        change (Scheme.Spec.map (CommRingCat.ofHom g).op).appTop ≫
          (Scheme.ΓSpecIso (CommRingCat.of E)).hom =
          (Scheme.ΓSpecIso D).hom ≫ CommRingCat.ofHom g at hnat
        rw [Category.assoc, hnat]
        simp
      rw [Category.assoc, hqmap]
      ext a
      rfl
    let _ : Algebra A Γ(P, ⊤) := p.appTop.hom.toAlgebra
    have hcomm : ∀ a : A, e.symm (algebraMap A E a) = algebraMap A (Γ(P, ⊤)) a := by
      intro a
      change e.symm ((g.comp fr) a) = p.appTop.hom a
      apply e.injective
      rw [RingEquiv.apply_symm_apply]
      symm
      change (Scheme.ΓSpecIso (CommRingCat.of E)).hom (p.appTop.hom a) = (g.comp fr) a
      have := congrArg (fun h : CommRingCat.of A ⟶ CommRingCat.of E => h.hom a) heq
      simpa [CommRingCat.comp_apply, φ, e] using this
    refine (indEtale_iff_ind_etale_underMk (R := CommRingCat.of A) (B := Γ(P, ⊤))).1 ?_
    exact StacksDraft.indEtale_of_equiv (RingEquiv.refl A) e.symm hcomm
      (indEtale_iff_ind_etale_underMk.2 hindAE)
  have hweakg : @Algebra.WeaklyEtale D E _ _ g.toAlgebra :=
    Algebra.weaklyEtale_of_ind_etale (indEtale_iff_ind_etale_underMk.2 hindDE)
  have hweakq : WeaklyEtale q := by
    have hs : WeaklyEtale (Scheme.Spec.map (CommRingCat.ofHom g).op) := by
      simpa using (weaklyEtale_specMap_iff (CommRingCat.ofHom g)).2 hweakg
    exact inferInstance
  let _ : AlgebraicGeometry.Surjective (Scheme.Spec.map (CommRingCat.ofHom g).op) := by
    exact ((flat_and_surjective_SpecMap_iff (CommRingCat.ofHom g)).mpr hff).2
  let _ : AlgebraicGeometry.Surjective q := by
    dsimp [q]
    exact ⟨(U.isoSpec.inv).surjective.comp
      (Scheme.Hom.surjective (Scheme.Spec.map (CommRingCat.ofHom g).op))⟩
  let _ : QuasiCompact q := by
    dsimp [q]
    infer_instance
  have hbound : Cardinal.mk PUnit ≤ B.coveringBound := by
    simpa using (B.covering_isSite.1 (𝟙 X.obj.left)).2
  let raw : PreZeroHypercover X.obj.left := { I₀ := PUnit, X _ := YB, f _ := qB }
  have hraw : B.IsProetaleCovering ⟨X.obj.left, raw⟩ := by
    change (raw.map B.inclusion).presieve₀ ∈ Scheme.proetalePrecoverage X.obj.left.obj
    have heq : (raw.map B.inclusion).presieve₀ = Presieve.singleton q := by
      change Presieve.ofArrows (fun _ : PUnit => B.inclusion.obj YB)
        (fun _ => B.inclusion.map qB) = _
      rw [hqB, Presieve.ofArrows_pUnit]
    rw [heq]
    exact Scheme.Hom.singleton_mem_propQCPrecoverage hweakq
  let Vsmall : SmallProetale B S.obj S.property :=
    ⟨Over.mk pB, by
      change WeaklyEtale (B.inclusion.map pB)
      rw [hpB]
      exact inferInstance⟩
  have hVind : ObjectProperty.ind.{u} (fun C : Under Γ(S.obj, ⊤) ↦ C.hom.hom.Etale)
      (Under.mk (B.inclusion.map Vsmall.obj.hom).appTop) := by
    have hmor : B.inclusion.map Vsmall.obj.hom = p := hpB
    rw [hmor]
    exact hindP
  let V : AffineIndEtaleProetale B S := ⟨Vsmall, ⟨isAffine_Spec _, hVind⟩⟩
  let aSmall : Vsmall ⟶ X := ObjectProperty.homMk <| Over.homMk qB (by
    change qB ≫ X.obj.hom = pB
    apply B.inclusion.map_injective
    rw [Functor.map_comp, hqB, hpB])
  let f : (inclusion B S).obj V ⟶ X := ObjectProperty.homMk aSmall.hom
  let ESmall : PreZeroHypercover X := { I₀ := PUnit, X _ := Vsmall, f _ := aSmall }
  have hESmall : SmallProetale.IsCovering B S.obj S.property ⟨X, ESmall⟩ := by
    change B.covering ⟨X.obj.left,
      (ESmall.map (SmallProetale.inclusion B S.obj S.property)).map
        (BigProetaleOver.forget B S.obj S.property)⟩
    have hMap : ((ESmall.map (SmallProetale.inclusion B S.obj S.property)).map
        (BigProetaleOver.forget B S.obj S.property)) = raw := by
      apply PreZeroHypercover.ext rfl
      all_goals
        simp [ESmall, aSmall, Vsmall, qB, SmallProetale.inclusion, BigProetaleOver.forget]
    rw [hMap]
    exact (B.covering_iff ⟨X.obj.left, raw⟩).2 ⟨hraw, hbound⟩
  have hgen : Sieve.generate ESmall.presieve₀ ∈
      (SmallProetale.precoverage B S.obj S.property).toGrothendieck X :=
    Precoverage.generate_mem_toGrothendieck ⟨ESmall, rfl, hESmall⟩
  have heq : ESmall.presieve₀ = Presieve.singleton aSmall := by
    change Presieve.ofArrows (fun _ : PUnit => Vsmall) (fun _ => aSmall) = _
    rw [Presieve.ofArrows_pUnit]
  rw [heq] at hgen
  have hf : aSmall = f := by
    ext
    rfl
  have hESmall' : SmallProetale.IsCovering B S.obj S.property
      ⟨X, PreZeroHypercover.singleton.{u + 1} f⟩ := by
    simpa [PreZeroHypercover.singleton, ESmall, hf] using hESmall
  exact ⟨V, f, hESmall', by simpa [hf] using hgen⟩

/-- A covering of an object of the small pro-étale site pulls back, along a morphism to it from
an affine ind-étale object, to a standard pro-étale covering each member of which factors
through the given covering. -/
private theorem finite_pullback_refinement [IsAffine S.obj] (X : AffineIndEtaleProetale B S)
    {U : SmallProetale B S.obj S.property} (a : (inclusion B S).obj X ⟶ U)
    (E : PreZeroHypercover.{u + 1} U)
    (hE : SmallProetale.IsCovering B S.obj S.property ⟨U, E⟩) :
    ∃ F : PreZeroHypercover.{u + 1} X,
      F.presieve₀ ∈ precoverage B S X ∧
        ∀ i, (Sieve.generate E.presieve₀).pullback a ((inclusion B S).map (F.f i)) := by
  classical
  let G := inclusion B S
  let forget := SmallProetale.inclusion B S.obj S.property ⋙
    BigProetaleOver.forget B S.obj S.property
  let E₀ : Covering B.Scheme := ⟨U.obj.left,
    { I₀ := E.I₀, X i := forget.obj (E.X i), f i := forget.map (E.f i) }⟩
  have hE₀ : B.covering E₀ := by
    simpa [E₀, forget, PreZeroHypercover.map, SmallProetale.inclusion,
      BigProetaleOver.forget] using hE
  let T := (G.obj X).obj.left
  obtain ⟨P, p₁, p₂, hpb, hP⟩ := B.covering_isSite.2.2 E₀ hE₀ T (forget.map a)
  let P₀ : PreZeroHypercover T := { I₀ := E₀.2.I₀, X i := P i, f i := p₂ i }
  have hP₀ : B.IsProetaleCovering ⟨T, P₀⟩ := by
    simpa [P₀, E₀, PreZeroHypercover.map] using hP.1
  let _ : IsAffine (B.inclusion.obj T) := X.property.1
  obtain ⟨Fstd, hF, hfinite, hFaff, hrefine⟩ := finite_standard_refinement B T P₀ hP₀
  have hweakF (i : Fstd.I₀) : WeaklyEtale (B.inclusion.map (Fstd.f i)) :=
    ((Scheme.ofArrows_mem_precoverage_iff (@WeaklyEtale)).mp hF.1.2).2 i
  let W (i : Fstd.I₀) : SmallProetale B S.obj S.property :=
    { obj := Over.mk (Fstd.f i ≫ (G.obj X).obj.hom)
      property := by
        change WeaklyEtale (B.inclusion.map (Fstd.f i ≫ (G.obj X).obj.hom))
        rw [Functor.map_comp]
        exact inferInstance }
  choose V g hEi hEiGen using fun i => exists_cover_affine B S (W i) (hFaff i)
  let Ei (i : Fstd.I₀) : PreZeroHypercover.{u + 1} (W i) :=
    PreZeroHypercover.singleton.{u + 1} (g i)
  let hi (i : Fstd.I₀) : W i ⟶ G.obj X := ObjectProperty.homMk (Over.homMk (Fstd.f i) (by rfl))
  let Fapp : PreZeroHypercover.{u + 1} X :=
    { I₀ := Σ i : Fstd.I₀, (Ei i).I₀
      X ij := V ij.1
      f ij := ObjectProperty.homMk (g ij.1 ≫ hi ij.1) }
  have hmap : ((Fapp.map G).map forget) = Fstd.bind (fun i => (Ei i).map forget) := by
    refine PreZeroHypercover.ext (x := (Fapp.map G).map forget)
      (y := Fstd.bind fun i => (Ei i).map forget) (by rfl) (by rfl) ?_
    apply heq_of_eq
    funext ij
    rcases ij with ⟨i, j⟩
    cases j
    rfl
  have hF'cover : SmallProetale.IsCovering B S.obj S.property ⟨G.obj X, Fapp.map G⟩ := by
    change B.covering ⟨T, (Fapp.map G).map forget⟩
    rw [hmap]
    exact B.covering_isSite.2.1 ⟨T, Fstd⟩ hF (fun i => ⟨Fstd.X i, (Ei i).map forget⟩) hEi
      (fun _ => rfl)
  have hF'finite : Finite Fapp.I₀ := by
    have hEiFinite (i : Fstd.I₀) : Finite (Ei i).I₀ := by
      dsimp [Ei, PreZeroHypercover.singleton]
      infer_instance
    infer_instance
  refine ⟨Fapp, ⟨Fapp, rfl, hF'cover, hF'finite⟩, ?_⟩
  intro ij
  obtain ⟨j, q, hq⟩ := hrefine ij.1
  let l : (forget.obj (G.obj (V ij.1))) ⟶ E₀.2.X j := forget.map (g ij.1) ≫ q ≫ p₁ j
  have hq' : q ≫ p₂ j = Fstd.f ij.1 := by simpa [P₀] using hq
  have hl : l ≫ E₀.2.f j = forget.map (g ij.1) ≫ Fstd.f ij.1 ≫ forget.map a := by
    calc
      l ≫ E₀.2.f j = forget.map (g ij.1) ≫ (q ≫ (p₁ j ≫ E₀.2.f j)) := by
        simp [l, Category.assoc]
      _ = forget.map (g ij.1) ≫ (q ≫ (p₂ j ≫ forget.map a)) := by rw [(hpb j).w]
      _ = (forget.map (g ij.1) ≫ q ≫ p₂ j) ≫ forget.map a := by simp
      _ = (forget.map (g ij.1) ≫ Fstd.f ij.1) ≫ forget.map a := by rw [hq']
      _ = forget.map (g ij.1) ≫ Fstd.f ij.1 ≫ forget.map a := by simp [Category.assoc]
  have hmapg : forget.map (G.map (Fapp.f ij)) = forget.map (g ij.1) ≫ Fstd.f ij.1 := by
    simp [Fapp, hi, G, inclusion, forget, SmallProetale.inclusion, BigProetaleOver.forget]
  have hOver : l ≫ (E.X j).obj.hom = (G.obj (V ij.1)).obj.hom := by
    calc
      l ≫ (E.X j).obj.hom = (l ≫ (E.f j).hom.left) ≫ U.obj.hom := by
        rw [← (E.f j).hom.w]
        simp only [Category.assoc]
      _ = (l ≫ E₀.2.f j) ≫ U.obj.hom := by
        simp [E₀, forget, SmallProetale.inclusion, BigProetaleOver.forget]
      _ = (forget.map (g ij.1) ≫ Fstd.f ij.1 ≫ forget.map a) ≫ U.obj.hom := by rw [hl]
      _ = forget.map (G.map (Fapp.f ij)) ≫ (forget.map a ≫ U.obj.hom) := by
        rw [hmapg]
        simp [Category.assoc]
      _ = forget.map (G.map (Fapp.f ij)) ≫ (G.obj X).obj.hom := by
        congr 1
        simp [forget, SmallProetale.inclusion, BigProetaleOver.forget]
      _ = (G.obj (V ij.1)).obj.hom := by
        simp [forget, SmallProetale.inclusion, BigProetaleOver.forget, Fapp]
  let lSmall : G.obj (V ij.1) ⟶ E.X j := ObjectProperty.homMk (Over.homMk l hOver)
  change (Sieve.generate E.presieve₀) ((G.map (Fapp.f ij)) ≫ a)
  have hfactor' : lSmall ≫ E.f j = G.map (Fapp.f ij) ≫ a := by
    apply forget.map_injective
    calc
      forget.map (lSmall ≫ E.f j) = l ≫ E₀.2.f j := by
        simp [lSmall, E₀, forget, SmallProetale.inclusion, BigProetaleOver.forget]
      _ = forget.map (g ij.1) ≫ Fstd.f ij.1 ≫ forget.map a := hl
      _ = forget.map (G.map (Fapp.f ij) ≫ a) := by
        simp [Functor.map_comp, hmapg, Category.assoc]
  exact ⟨E.X j, lSmall, E.f j, E.presieve₀_f j, hfactor'⟩

/-- A covering sieve of the small pro-étale site pulls back, along any morphism from an affine
ind-étale object, to a covering sieve of the affine ind-étale site. -/
private theorem inclusion_lifts_saturate [IsAffine S.obj]
    {U : SmallProetale B S.obj S.property} {R : Sieve U}
    (hR : (SmallProetale.precoverage B S.obj S.property).Saturate U R) :
    ∀ {X : AffineIndEtaleProetale B S} (a : (inclusion B S).obj X ⟶ U),
      (R.pullback a).functorPullback (inclusion B S) ∈ topology B S X := by
  induction hR with
  | of U P hP =>
      intro X a
      obtain ⟨E, rfl, hE⟩ := (SmallProetale.mem_precoverage_iff B S.obj S.property).mp hP
      obtain ⟨F, hF, hfactor⟩ := finite_pullback_refinement B S X a E hE
      apply (topology B S).superset_covering ?_ (Precoverage.Saturate.of X F.presieve₀ hF)
      rw [Sieve.generate_le_iff]
      intro Y f hf
      obtain ⟨i⟩ := hf
      exact hfactor i
  | top U =>
      intro X a
      simpa only [Sieve.pullback_top, Sieve.functorPullback_top] using (topology B S).top_mem X
  | pullback U R hR Y f ih =>
      intro X a
      simpa [Sieve.pullback_comp, Category.assoc] using ih (a ≫ f)
  | transitive U R T hR hlocal ih ihlocal =>
      intro X a
      refine (topology B S).transitive (ih a)
        ((T.pullback a).functorPullback (inclusion B S)) ?_
      intro Z k hk
      have hk' : R ((inclusion B S).map k ≫ a) := hk
      have hsat := ihlocal hk' (a := 𝟙 _)
      rw [← Sieve.functorPullback_pullback]
      simpa [Sieve.pullback_comp, Category.assoc] using hsat

/-- **Stacks 098X.** The affine ind-étale objects are cover-dense in the small pro-étale site:
every object is covered by affine ones, and every affine one is covered by an affine ind-étale
one. -/
theorem inclusion_isCoverDense [IsAffine S.obj] :
    (inclusion B S).IsCoverDense (SmallProetale.topology B S.obj S.property) := by
  classical
  let G := inclusion B S
  let K := SmallProetale.topology B S.obj S.property
  refine ⟨?_⟩
  intro X
  let U := B.inclusion.obj X.obj.left
  let A := U.affineCover
  let Q : PreZeroHypercover X.obj.left :=
    { I₀ := ULift.{u + 1, u} A.I₀
      X i := ⟨A.X i.down, Scheme.size_lt_of_isOpenImmersion (A.f i.down) X.obj.left.property⟩
      f i := B.inclusion.preimage (show
        B.inclusion.obj ⟨A.X i.down,
          Scheme.size_lt_of_isOpenImmersion (A.f i.down) X.obj.left.property⟩ ⟶
            B.inclusion.obj X.obj.left from A.f i.down) }
  have hpres : (Q.map B.inclusion).presieve₀ = A.toPreZeroHypercover.presieve₀ := by
    apply le_antisymm
    · rw [Presieve.ofArrows_le_iff]
      intro i
      have heq : B.inclusion.map (Q.f i) = A.toPreZeroHypercover.f i.down := by
        change B.inclusion.map (B.inclusion.preimage (show
          B.inclusion.obj (Q.X i) ⟶ B.inclusion.obj X.obj.left from A.f i.down)) = _
        rw [Functor.map_preimage]
      change A.toPreZeroHypercover.presieve₀ (B.inclusion.map (Q.f i))
      rw [heq]
      exact A.toPreZeroHypercover.presieve₀_f _
    · rw [Presieve.ofArrows_le_iff]
      intro i
      have heq : B.inclusion.map (Q.f (ULift.up i)) = A.toPreZeroHypercover.f i := by
        change B.inclusion.map (B.inclusion.preimage (show
          B.inclusion.obj (Q.X (ULift.up i)) ⟶ B.inclusion.obj X.obj.left from A.f i)) = _
        rw [Functor.map_preimage]
      change (Q.map B.inclusion).presieve₀ (A.toPreZeroHypercover.f i)
      rw [← heq]
      exact (Q.map B.inclusion).presieve₀_f _
  have hzle : Scheme.zariskiPrecoverage ≤ Scheme.proetalePrecoverage := by
    rw [Scheme.proetalePrecoverage]
    change Scheme.zariskiPrecoverage ≤ Scheme.qcPrecoverage ⊓ Scheme.precoverage @WeaklyEtale
    refine le_inf Scheme.zariskiPrecoverage_le_qcPrecoverage ?_
    exact Scheme.precoverage_mono fun Y Z f hf => by infer_instance
  have hQ : B.IsProetaleCovering ⟨X.obj.left, Q⟩ := by
    rw [B.isProetaleCovering_iff, hpres]
    exact hzle _ A.mem₀
  obtain ⟨⟨Y, F⟩, hF, hcomb⟩ := B.covering_representatives ⟨X.obj.left, Q⟩ hQ
  have hY : Y = X.obj.left := hcomb.1.symm
  subst hY
  obtain ⟨β, hX, hf⟩ := hcomb.2.2
  let EObj (i : F.I₀) : SmallProetale B S.obj S.property :=
    { obj := Over.mk (F.f i ≫ X.obj.hom)
      property := by
        change WeaklyEtale (B.inclusion.map (F.f i ≫ X.obj.hom))
        rw [Functor.map_comp]
        have hopen : IsOpenImmersion (B.inclusion.map (Q.f (β i))) := by
          change IsOpenImmersion (B.inclusion.map (B.inclusion.preimage (show
            B.inclusion.obj (Q.X (β i)) ⟶ B.inclusion.obj X.obj.left from A.f (β i).down)))
          rw [Functor.map_preimage]
          exact A.map_prop (β i).down
        have hweakF : WeaklyEtale (B.inclusion.map (F.f i)) := by
          rw [hf i, Functor.map_comp]
          infer_instance
        infer_instance }
  let E : PreZeroHypercover X :=
    { I₀ := F.I₀
      X := EObj
      f i := ObjectProperty.homMk (Over.homMk (F.f i) (by rfl)) }
  have hmapE : (E.map (SmallProetale.inclusion B S.obj S.property)).map
      (BigProetaleOver.forget B S.obj S.property) = F := by
    apply PreZeroHypercover.ext rfl
    all_goals simp [E, EObj, SmallProetale.inclusion, Over.forget]
  have hE : SmallProetale.IsCovering B S.obj S.property ⟨X, E⟩ := by
    change B.covering ⟨X.obj.left,
      (E.map (SmallProetale.inclusion B S.obj S.property)).map
        (BigProetaleOver.forget B S.obj S.property)⟩
    rw [hmapE]
    exact hF
  have hgen : Sieve.generate E.presieve₀ ∈ K X :=
    Precoverage.generate_mem_toGrothendieck ⟨E, rfl, hE⟩
  let T := Sieve.coverByImage G X
  have hAffine (i : F.I₀) : IsAffine (B.inclusion.obj (F.X i)) := by
    rw [hX i]
    change IsAffine (A.X (β i).down)
    infer_instance
  have hpull (i : F.I₀) : T.pullback (E.f i) ∈ K (E.X i) := by
    obtain ⟨V, g, -, hg⟩ := exists_cover_affine B S (E.X i) (hAffine i)
    apply K.superset_covering ?_ hg
    rw [Sieve.generate_le_iff]
    rintro Z a ⟨⟩
    exact Presieve.in_coverByImage (G := G) (Y := V) (g ≫ E.f i)
  apply K.transitive hgen T
  intro Z a ha
  obtain ⟨Y', b, c, hb, rfl⟩ := ha
  obtain ⟨i⟩ := hb
  simpa [Sieve.pullback_comp] using K.pullback_stable b (hpull i)

/-- **Stacks 098X.** The topology of the affine ind-étale site is the topology induced from the
small pro-étale site. -/
theorem topology_eq_restricted [IsAffine S.obj] :
    topology B S = (inclusion B S).restrictedTopology
      (SmallProetale.topology B S.obj S.property) := by
  let G := inclusion B S
  let P := precoverage B S
  let Q := SmallProetale.precoverage B S.obj S.property
  let K := SmallProetale.topology B S.obj S.property
  have hpre : P ≤ Q.comap G := by
    intro X R hR
    obtain ⟨E, hEq, hE⟩ := hR
    rw [Precoverage.mem_comap_iff, hEq, ← PreZeroHypercover.presieve₀_map,
      SmallProetale.mem_precoverage_iff]
    exact ⟨E.map G, rfl, hE.1⟩
  let _ : G.IsCoverDense K := inclusion_isCoverDense B S
  have hle : P.toGrothendieck ≤ G.restrictedTopology K :=
    (Precoverage.toGrothendieck_monotone hpre).trans Q.toGrothendieck_comap_le_restrictedTopology
  have hge : G.restrictedTopology K ≤ P.toGrothendieck := by
    intro X R hR
    rw [Functor.mem_restrictedTopology_iff] at hR
    have hlift := inclusion_lifts_saturate B S (hR : Q.Saturate (G.obj X) _) (𝟙 _)
    rw [Sieve.pullback_id, Sieve.functorPullback_functorPushforward_eq G] at hlift
    exact hlift
  exact le_antisymm hle hge

/-- The inclusion of the affine ind-étale site into the small pro-étale site preserves covering
sieves. -/
theorem inclusion_coverPreserving [IsAffine S.obj] :
    CoverPreserving (topology B S) (SmallProetale.topology B S.obj S.property)
      (inclusion B S) := by
  let G := inclusion B S
  let K := SmallProetale.topology B S.obj S.property
  let _ : G.IsCoverDense K := inclusion_isCoverDense B S
  rw [topology_eq_restricted B S]
  exact G.coverPreserving_restrictedTopology K

/-- **Stacks 098X.** Restriction along the inclusion takes pro-étale sheaves to sheaves on the
affine ind-étale site. -/
@[stacks 098X "restriction preserves sheaves"]
instance inclusion_isContinuous [IsAffine S.obj] :
    (inclusion B S).IsContinuous (topology B S)
      (SmallProetale.topology B S.obj S.property) := by
  let G := inclusion B S
  let K := SmallProetale.topology B S.obj S.property
  let _ : G.IsCoverDense K := inclusion_isCoverDense B S
  exact Functor.IsCoverDense.isContinuous (topology B S) K G (inclusion_coverPreserving B S)

/-- **Stacks 098X.** Restriction from the small pro-étale site to the affine ind-étale subsite
is an equivalence of categories of sheaves of sets. -/
@[stacks 098X "restriction is an equivalence of topoi"]
instance isEquivalence_restriction [IsAffine S.obj] :
    ((inclusion B S).sheafPushforwardContinuous (Type (max u v))
      (topology B S) (SmallProetale.topology B S.obj S.property)).IsEquivalence := by
  let _ : (inclusion B S).IsCoverDense (SmallProetale.topology B S.obj S.property) :=
    inclusion_isCoverDense B S
  have _ : (inclusion B S).IsDenseSubsite (topology B S)
      (SmallProetale.topology B S.obj S.property) := by
    rw [topology_eq_restricted B S]
    infer_instance
  have _ : ∀ X : (SmallProetale B S.obj S.property)ᵒᵖ,
      Limits.HasLimitsOfShape (StructuredArrow X (inclusion B S).op) (Type (max u v)) := by
    intro X
    have _ : EssentiallySmall.{max u v} (AffineIndEtaleProetale B S) := essentiallySmall B S
    exact CategoryTheory.Limits.HasLimitsOfShape.of_essentiallySmall.{max u v, max u v, u,
      u + 1, max u v, max u v + 1}
      (C := Type (max u v)) (J := StructuredArrow X (inclusion B S).op)
  infer_instance

end AffineIndEtaleProetale

end AlgebraicGeometry.ProEtale
