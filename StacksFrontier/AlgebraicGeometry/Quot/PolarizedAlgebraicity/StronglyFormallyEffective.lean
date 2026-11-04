module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedFormalEffective
public import StacksFrontier.Deformation.Artin.FormalObject.Effectiveness

/-!
# `𝒫olarized` is strongly formally effective

Strong formal effectiveness (`Deformation.Artin.IsStronglyFormallyEffective`) asks that every
system of objects `ξₙ` of a category fibred in groupoids over the spectra of an inverse system
`Rₙ` of algebras over an affine open `Spec Λ ⊆ S`, with surjective transition maps whose kernels
are locally nilpotent, together with the cocone of its base schemes onto `Spec(lim Rₙ)`, come from
an object over `Spec(lim Rₙ)`. For the stack `𝒫olarized` of polarized proper schemes this is the
algebraization of polarized formal families
(`Stacks.PolarizedAlgebraization.exists_algebraization`): a morphism of polarized families is a
cartesian square with an isomorphism of polarizations, so a system of polarized families over the
`Spec Rₙ` is exactly the input of that algebraization, and the algebraization it produces is the
object over `Spec(lim Rₙ)`.

## Main results

* `AlgebraicGeometry.PolarizedAlgebraicity.preservesLimits_forget₂_commAlgCat`: the forgetful
  functor from commutative `Λ`-algebras to commutative rings preserves limits.
* `AlgebraicGeometry.PolarizedAlgebraicity.isLimit_forget₂_mapCone`: the underlying cone of rings
  of a limit cone of commutative algebras is a limit.
* `AlgebraicGeometry.PolarizedAlgebraicity.isStronglyFormallyEffective_polarizedSliceProjection`:
  `𝒫olarized` over a terminal base is strongly formally effective.

## References

* [Stacks Project, Tag 0CXT](https://stacks.math.columbia.edu/tag/0CXT)
* [Stacks Project, Tag 0D4T](https://stacks.math.columbia.edu/tag/0D4T)
* [Stacks Project, Tag 0D4V](https://stacks.math.columbia.edu/tag/0D4V)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Ample

universe u

namespace AlgebraicGeometry.PolarizedAlgebraicity

/-- The forgetful functor from commutative `Λ`-algebras to commutative rings preserves
limits. -/
theorem preservesLimits_forget₂_commAlgCat (Λ : Type u) [CommRing Λ] :
    PreservesLimits (forget₂ (CommAlgCat.{u} Λ) CommRingCat.{u}) := by
  let F : CommAlgCat.{u} Λ ⥤ CommRingCat.{u} := forget₂ (CommAlgCat.{u} Λ) CommRingCat.{u}
  let G : CommAlgCat.{u} Λ ⥤ CommRingCat.{u} :=
    (commAlgCatEquivUnder (CommRingCat.of Λ)).functor ⋙ Under.forget (CommRingCat.of Λ)
  have hiso : F ≅ G :=
    NatIso.ofComponents (fun A => Iso.refl _) (fun {A B} f => by
      dsimp [F, G, commAlgCatEquivUnder, CommRingCat.mkUnder]
      rfl)
  exact preservesLimits_of_natIso hiso.symm

/-- **The underlying cone of rings of a limit cone of commutative algebras is a limit.** -/
def isLimit_forget₂_mapCone {Λ : Type u} [CommRing Λ] {J : Type} [SmallCategory J]
    {F : J ⥤ CommAlgCat.{u} Λ} {c : Cone F} (hc : IsLimit c) :
    IsLimit ((forget₂ (CommAlgCat.{u} Λ) CommRingCat.{u}).mapCone c) :=
  haveI := preservesLimits_forget₂_commAlgCat.{u} Λ
  haveI : PreservesLimitsOfSize.{0, 0} (forget₂ (CommAlgCat.{u} Λ) CommRingCat.{u}) :=
    preservesLimitsOfSize_shrink _
  isLimitOfPreserves _ hc

variable (B : BigFppfSite.{u}) {S : Scheme.{u}} (hS : B.Contains S) (hT : IsTerminal (B.obj hS))

/-- **`𝒫olarized` is strongly formally effective.** A system of
polarized families over the spectra of an inverse system of algebras with surjective transition
maps and locally nilpotent kernels is algebraized over the spectrum of the limit, and the
algebraization, with its identifications on the levels, is the cocone of `𝒫olarized` lifting the
given cocone of base schemes. -/
theorem isStronglyFormallyEffective_polarizedSliceProjection [IsLocallyNoetherian S] :
    Deformation.Artin.IsStronglyFormallyEffective B S hS (polarizedSliceProjection B hS hT)
      (polarizedProjection_isFiberedInGroupoids_unconditional.sliceAtTerminal hT) := by
  rintro Λ _ chart _ R cR hcR hsurj hnil ξ ⟨⟨ptl, ⟨⟨⟩⟩, pth⟩, ι⟩ e eLimit he heLimit -
  obtain rfl : pth = hT.from ptl := hT.hom_ext _ _
  let A : ℕᵒᵖ ⥤ CommRingCat.{u} := R ⋙ forget₂ (CommAlgCat.{u} Λ) CommRingCat.{u}
  have hA := isLimit_forget₂_mapCone hcR
  let g : ∀ n : ℕ, n ⟶ n + 1 := fun n => homOfLE (Nat.le_succ n)
  let X : ℕ → Scheme.{u} := fun n => (ξ.obj n).total
  let e₁ : ∀ n, B.inclusion.obj (ξ.obj n).base ≅ Spec (A.obj (op n)) := e
  let f : ∀ n, X n ⟶ Spec (A.obj (op n)) := fun n => (ξ.obj n).toBase ≫ (e₁ n).hom
  have hbase : ∀ {m n : ℕ} (k : m ⟶ n),
      B.inclusion.map (ξ.map k).baseMap ≫ (e₁ n).hom = (e₁ m).hom ≫ Spec.map (A.map k.op) :=
    fun k => he k
  have hpb : ∀ n, IsPullback (ξ.map (g n)).totalMap (f n) (f (n + 1))
      (Spec.map (A.map (g n).op)) := fun n =>
    (ξ.map (g n)).cartesian.of_iso (Iso.refl _) (Iso.refl _) (e₁ n) (e₁ (n + 1)) (by simp)
      (by simp [f]) (by simp [f]) (hbase (g n))
  have hproper : ∀ n, IsProper (f n) := fun n => by
    have := (ξ.obj n).proper
    dsimp only [f]
    infer_instance
  have hflat : ∀ n, Flat (f n) := fun n => by
    have := (ξ.obj n).flat
    dsimp only [f]
    infer_instance
  have hfp : ∀ n, FinitePresentation (f n) := fun n => by
    obtain ⟨_, _, _⟩ := (ξ.obj n).finitePresentation
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  have hL : ∀ n, IsInvertibleModule (X n) (ξ.obj n).lineBundle := fun n => (ξ.obj n).invertible
  have hample : IsAmple (X 0) (ξ.obj 0).lineBundle := by
    let := hL 0
    have : IsAffine (B.inclusion.obj (ξ.obj 0).base) := IsAffine.of_isIso (e₁ 0).hom
    exact (Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple _ _).mp
      (ξ.obj 0).relativelyAmple
  have hnil' : ∀ n : ℕ, RingHom.ker (A.map (g n).op).hom ≤ nilradical (A.obj (op (n + 1))) :=
    fun n x hx => mem_nilradical.mpr (hnil (g n).op x hx)
  obtain ⟨Y, gY, ℒ, hℒ, j, hj, e', hproperY, hflatY, hfpY, hampleY, hpbY, hiso, hcompat⟩ :=
    Stacks.PolarizedAlgebraization.exists_algebraization A (fun n => hsurj (g n).op) hnil' X f
      (fun n => (ξ.map (g n)).totalMap) hpb (fun n => (ξ.obj n).lineBundle) (hL := hL)
      (fun n => (ξ.map (g n)).lineBundleIso) (hproper := hproper) (hflat := hflat) hfp hample
  have := hproperY
  have := hflatY
  let ε : (forget₂ (CommAlgCat.{u} Λ) CommRingCat.{u}).obj cR.pt ≅ limit A :=
    hA.conePointUniqueUpToIso (limit.isLimit A)
  let e₀ : Spec (limit A) ≅ B.inclusion.obj ptl := Scheme.Spec.mapIso ε.op ≪≫ eLimit.symm
  have : IsAffine (B.inclusion.obj ptl) := IsAffine.of_isIso e₀.inv
  let x : PolarizedFamily B :=
    { base := ptl
      total := Y
      toBase := gY ≫ e₀.hom
      proper := inferInstance
      flat := inferInstance
      finitePresentation := by
        obtain ⟨_, _, _⟩ := hfpY
        exact ⟨inferInstance, inferInstance, inferInstance⟩
      lineBundle := ℒ
      invertible := hℒ
      relativelyAmple := (Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple _ _).mpr
        hampleY }
  have hπ : ∀ n : ℕ, Spec.map (limit.π A (op n)) ≫ e₀.hom =
      (e₁ n).inv ≫ B.inclusion.map (ι.app n).left := fun n => by
    have hε : ε.hom ≫ limit.π A (op n) =
        (forget₂ (CommAlgCat.{u} Λ) CommRingCat.{u}).map (cR.π.app (op n)) :=
      hA.conePointUniqueUpToIso_hom_comp (limit.isLimit A) (op n)
    have h1 : Spec.map (limit.π A (op n)) ≫ Spec.map ε.hom =
        Spec.map ((forget₂ (CommAlgCat.{u} Λ) CommRingCat.{u}).map (cR.π.app (op n))) := by
      rw [← Spec.map_comp, hε]
    simp only [e₀, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.op_hom,
      Scheme.Spec_map, Quiver.Hom.unop_op]
    rw [← Category.assoc, h1, Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
    exact (heLimit n).symm
  let L : ∀ n, ξ.obj n ⟶ x := fun n =>
    { baseMap := (ι.app n).left
      totalMap := j n
      cartesian := (hpbY n).of_iso (Iso.refl _) (Iso.refl _) (e₁ n).symm e₀ (by simp)
        (by simp [f]) (by simp [x]) (hπ n)
      lineBundleIso := @asIso _ _ _ _ (e' n) (hiso n) }
  have hL' : ∀ n, ξ.map (g n) ≫ L (n + 1) = L n ≫ ((Functor.const ℕ).obj x).map (g n) := by
    intro n
    refine Eq.trans ?_ (Category.comp_id (L n)).symm
    refine PolarizedFamily.Hom.ext ?_ (hj n) ?_
    · have h := congrArg CommaMorphism.left (ι.naturality (g n))
      simp only [Functor.const_obj_map, Over.comp_left] at h
      exact h
    · refine PolarizedFormal.heq_of_pullbackCongr_hom_app_comp (hj n) _ _ ?_
      show (Scheme.Modules.pullbackCongr (hj n)).hom.app ℒ ≫ e' n =
        (Scheme.Modules.pullbackComp _ _).inv.app ℒ ≫
          (Scheme.Modules.pullback (ξ.map (g n)).totalMap).map (e' (n + 1)) ≫
            (ξ.map (g n)).lineBundleIso.hom
      rw [← hcompat n, ← Category.assoc, ← NatTrans.comp_app, Iso.inv_hom_id, NatTrans.id_app,
        Category.id_comp]
  exact ⟨⟨x, NatTrans.ofSequence L hL'⟩, rfl⟩

end AlgebraicGeometry.PolarizedAlgebraicity

end
