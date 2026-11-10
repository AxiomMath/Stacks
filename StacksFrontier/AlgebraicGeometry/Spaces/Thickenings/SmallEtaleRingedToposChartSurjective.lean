module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineRefinement
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSchemeStructureSharp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleTwoIsoAffineCover
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.RangeDescent

/-!
# A surjective structure map is surjective on affine charts with affine base change

Let `i : Z ⟶ Z'` be a representable morphism of algebraic spaces over a scheme `S` whose
structure map `i♯ : 𝒪_{Z'} ⟶ i_*𝒪_Z` (Stacks 03G8) is surjective, that is locally surjective on
the small étale site of `Z'`.  Let `V` be an affine étale chart of `Z'` over which the base change
of `i`, and the base change of `i` over every affine étale chart above `V`, are affine.  Then the
map `Γ(V) ⟶ Γ(Z ×_{Z'} V)` is surjective.

Through Stacks 03G8, part (2) the structure map over a chart `W` is pullback of functions along
`Z ×_{Z'} W ⟶ W`.  A function `b` on `Z ×_{Z'} V` comes, on the members of a covering sieve of
`V`, from functions on the members; finitely many affine members `W_k` already cover `V`
(`AlgebraicGeometry.Space.SmallEtale.exists_finite_affine_etale_ofArrows_le`), and they are étale,
hence flat, over `V`.  Since `Γ(Z ×_{Z'} W_k) = Γ(W_k) ⊗_{Γ(V)} Γ(Z ×_{Z'} V)`, faithfully flat
descent (`Stacks.RangeDescent.mem_range_of_isPushout_cover`) shows that `b` comes from `Γ(V)`.

## Main results

* `AlgebraicGeometry.Space.surjective_appTop_snd_of_isLocallySurjective_fSharp`: the statement
  above.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 0D16](https://stacks.math.columbia.edu/tag/0D16)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The structure map of a representable morphism, read through the base-changed charts, is
locally surjective as soon as the structure map is. -/
theorem isLocallySurjective_cartesianProjectionSharp {Z Z' : AlgebraicSpaces B S hS}
    (i : Z ⟶ Z') (hrep : yoneda.relativelyRepresentable i.hom)
    (hsurj : Presheaf.IsLocallySurjective (SmallEtale.topology B S hS Z'.1)
      (smallEtaleRingedToposHom B S hS i).fSharp.hom) :
    letI := isContinuous_smallBaseChange B S hS i hrep
    Presheaf.IsLocallySurjective (SmallEtale.topology B S hS Z'.1)
      (cartesianProjectionSharp B S hS i hrep).hom := by
  let := isContinuous_smallBaseChange B S hS i hrep
  have h1 : Presheaf.IsLocallySurjective (SmallEtale.topology B S hS Z'.1)
      ((sheafCompose (SmallEtale.topology B S hS Z'.1)
        (forget₂ CommRingCat.{u} RingCat.{u})).map
          (smallEtaleRingedToposHom B S hS i).fSharp).hom := by
    rw [Presheaf.isLocallySurjective_iff_whisker_forget] at hsurj ⊢
    exact hsurj
  rw [← fSharp_comp_chartProjectionSharpDirectImage B S hS i hrep]
  have := h1
  have : IsIso (chartProjectionSharpDirectImage B S hS i hrep).hom := inferInstance
  have h2 : Presheaf.IsLocallySurjective (SmallEtale.topology B S hS Z'.1)
      (chartProjectionSharpDirectImage B S hS i hrep).hom :=
    Presheaf.isLocallySurjective_of_iso _ _
  change Presheaf.IsLocallySurjective _
    (((sheafCompose (SmallEtale.topology B S hS Z'.1) (forget₂ CommRingCat.{u} RingCat.{u})).map
      (smallEtaleRingedToposHom B S hS i).fSharp).hom ≫
        (chartProjectionSharpDirectImage B S hS i hrep).hom)
  exact @Presheaf.isLocallySurjective_comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2

/-- **A surjective structure map is surjective on an affine chart with affine base changes.**
Let `i : Z ⟶ Z'` be representable with surjective structure map, and `V` an affine étale chart
of `Z'` such that the base change of `i` over every affine étale chart of `Z'` is affine.  Then
pullback of functions `Γ(V) ⟶ Γ(Z ×_{Z'} V)` is surjective. -/
theorem surjective_appTop_snd_of_isLocallySurjective_fSharp {Z Z' : AlgebraicSpaces B S hS}
    (i : Z ⟶ Z') (hrep : yoneda.relativelyRepresentable i.hom)
    (hsurj : Presheaf.IsLocallySurjective (SmallEtale.topology B S hS Z'.1)
      (smallEtaleRingedToposHom B S hS i).fSharp.hom)
    (haff : ∀ W : SmallEtale B S hS Z'.1, IsAffine
        (((BigFppfOver.toScheme B S hS).obj W.obj.left)) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj (hrep.pullback W.obj.hom)))
    (V : SmallEtale B S hS Z'.1) (hV : IsAffine (((BigFppfOver.toScheme B S hS).obj V.obj.left))) :
    Function.Surjective ((BigFppfOver.toScheme B S hS).map (hrep.snd V.obj.hom)).appTop := by
  classical
  let := isContinuous_smallBaseChange B S hS i hrep
  have hcps := isLocallySurjective_cartesianProjectionSharp i hrep hsurj
  intro b
  obtain ⟨n, z, φ, hzaff, hzS, -, hcov⟩ :=
    SmallEtale.exists_finite_affine_etale_ofArrows_le B S hS Z'.1 hV
      (Presheaf.imageSieve_mem (SmallEtale.topology B S hS Z'.1)
        (cartesianProjectionSharp B S hS i hrep).hom b)
  obtain ⟨hjs, het⟩ := (Scheme.ofArrows_mem_precoverage_iff (P := @Etale)).1 hcov
  have := hV
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (hrep.pullback V.obj.hom)) := haff V hV
  have : ∀ k, IsAffine (((BigFppfOver.toScheme B S hS).obj (z k).obj.left)) := hzaff
  have : ∀ k, IsAffine ((BigFppfOver.toScheme B S hS).obj (hrep.pullback (z k).obj.hom)) :=
    fun k => haff (z k) (hzaff k)
  let fV := ((BigFppfOver.toScheme B S hS).map (hrep.snd V.obj.hom)).appTop
  let fz : ∀ k, _ := fun k => ((BigFppfOver.toScheme B S hS).map (hrep.snd (z k).obj.hom)).appTop
  let gφ : ∀ k, _ := fun k => ((BigFppfOver.toScheme B S hS).map (φ k).hom.left).appTop
  let hφ : ∀ k, _ := fun k => ((BigFppfOver.toScheme B S hS).map
    ((smallBaseChange B S hS i hrep).map (φ k)).hom.left).appTop
  let : Algebra Γ(((BigFppfOver.toScheme B S hS).obj V.obj.left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj
      (hrep.pullback V.obj.hom), ⊤) := fV.hom.toAlgebra
  let : ∀ k, Algebra Γ(((BigFppfOver.toScheme B S hS).obj V.obj.left), ⊤)
      Γ(((BigFppfOver.toScheme B S hS).obj (z k).obj.left), ⊤) := fun k => (gφ k).hom.toAlgebra
  let : ∀ k, Algebra Γ((BigFppfOver.toScheme B S hS).obj (hrep.pullback V.obj.hom), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (hrep.pullback (z k).obj.hom), ⊤) :=
    fun k => (hφ k).hom.toAlgebra
  let : ∀ k, Algebra Γ(((BigFppfOver.toScheme B S hS).obj (z k).obj.left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (hrep.pullback (z k).obj.hom), ⊤) :=
    fun k => (fz k).hom.toAlgebra
  let : ∀ k, Algebra Γ(((BigFppfOver.toScheme B S hS).obj V.obj.left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (hrep.pullback (z k).obj.hom), ⊤) :=
    fun k => ((gφ k) ≫ (fz k)).hom.toAlgebra
  have hsq : ∀ k, IsPullback
      ((BigFppfOver.toScheme B S hS).map ((smallBaseChange B S hS i hrep).map (φ k)).hom.left)
      ((BigFppfOver.toScheme B S hS).map (hrep.snd (z k).obj.hom))
      ((BigFppfOver.toScheme B S hS).map (hrep.snd V.obj.hom))
      ((BigFppfOver.toScheme B S hS).map (φ k).hom.left) :=
    fun k => isPullback_smallBaseChange_map B S hS i hrep (φ k)
  have hpush : ∀ k, IsPushout fV (gφ k) (hφ k) (fz k) :=
    fun k => isPushout_appTop_of_isPullback (hsq k)
  have : ∀ k, IsScalarTower Γ(((BigFppfOver.toScheme B S hS).obj V.obj.left), ⊤)
      Γ(((BigFppfOver.toScheme B S hS).obj (z k).obj.left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (hrep.pullback (z k).obj.hom), ⊤) :=
    fun k => IsScalarTower.of_algebraMap_eq' rfl
  have : ∀ k, IsScalarTower Γ(((BigFppfOver.toScheme B S hS).obj V.obj.left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (hrep.pullback V.obj.hom), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (hrep.pullback (z k).obj.hom), ⊤) :=
    fun k => IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom (hpush k).w).symm
  have : ∀ k, Algebra.IsPushout Γ(((BigFppfOver.toScheme B S hS).obj V.obj.left), ⊤)
      Γ(((BigFppfOver.toScheme B S hS).obj (z k).obj.left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (hrep.pullback V.obj.hom), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (hrep.pullback (z k).obj.hom), ⊤) :=
    fun k => (CommRingCat.isPushout_iff_isPushout).1 (hpush k).flip
  have : ∀ k, Module.Flat Γ(((BigFppfOver.toScheme B S hS).obj V.obj.left), ⊤)
      Γ(((BigFppfOver.toScheme B S hS).obj (z k).obj.left), ⊤) := fun k =>
    have : Etale ((BigFppfOver.toScheme B S hS).map (φ k).hom.left) := het k
    HasRingHomProperty.appTop @Flat (f := (BigFppfOver.toScheme B S hS).map (φ k).hom.left)
      inferInstance
  have hcovp : ∀ p : PrimeSpectrum Γ(((BigFppfOver.toScheme B S hS).obj V.obj.left), ⊤), ∃ k,
      ∃ q : PrimeSpectrum Γ(((BigFppfOver.toScheme B S hS).obj (z k).obj.left), ⊤),
        PrimeSpectrum.comap (algebraMap Γ(((BigFppfOver.toScheme B S hS).obj V.obj.left), ⊤)
            Γ(((BigFppfOver.toScheme B S hS).obj (z k).obj.left), ⊤)) q = p := by
    intro p
    obtain ⟨k, w, hw⟩ := hjs ((((BigFppfOver.toScheme B S hS).obj V.obj.left)).isoSpec.inv.base p)
    refine ⟨k, (((BigFppfOver.toScheme B S hS).obj (z k).obj.left)).toSpecΓ.base w, ?_⟩
    have h := congrArg (fun m => m.base w)
      (Scheme.toSpecΓ_naturality ((BigFppfOver.toScheme B S hS).map (φ k).hom.left))
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h
    change ((BigFppfOver.toScheme B S hS).map (φ k).hom.left) w = _ at hw
    rw [hw] at h
    change (Spec.map (gφ k)).base _ = p
    rw [← h]
    have hi := congrArg (fun f => f.base p)
      ((BigFppfOver.toScheme B S hS).obj V.obj.left).isoSpec.inv_hom_id
    exact hi
  have hb : ∀ k, ∃ a : Γ(((BigFppfOver.toScheme B S hS).obj (z k).obj.left), ⊤),
      algebraMap Γ((BigFppfOver.toScheme B S hS).obj (hrep.pullback V.obj.hom), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj (hrep.pullback (z k).obj.hom), ⊤) b =
        algebraMap Γ(((BigFppfOver.toScheme B S hS).obj (z k).obj.left), ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj (hrep.pullback (z k).obj.hom), ⊤) a := by
    intro k
    obtain ⟨a, ha⟩ := hzS k
    exact ⟨a, ha.symm⟩
  obtain ⟨a, ha⟩ := Stacks.RangeDescent.mem_range_of_isPushout_cover
    (fun k => Γ(((BigFppfOver.toScheme B S hS).obj (z k).obj.left), ⊤))
    (fun k => Γ((BigFppfOver.toScheme B S hS).obj (hrep.pullback (z k).obj.hom), ⊤))
    hcovp b hb
  exact ⟨a, ha⟩

end AlgebraicGeometry.Space

end
