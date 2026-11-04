module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.Comap
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.Immersions
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.RegularSliceThroughPoint

/-!
# Slicing by global sections

The scheme-level slicing lemma Stacks 06LI starts from germs at a point and produces its own
sections on an affine open.  When the germs are those of *global* sections `f₁, …, f_r` of `X`,
as in Stacks 06LW and 06MD, one wants the zero scheme of the restrictions of the `f_i`
themselves.  This file shrinks the affine open of Stacks 06LI to an affine open on which the
sections it produces agree with the restrictions of the `f_i`, and restricts the zero scheme
along the inclusion.

## Main results

* `Stacks.AlgebraicGeometry.exists_affine_openImmersion_flat_zeroScheme_of_isRegular_fiber`:
  if `g : X ⟶ S` is locally of finite presentation and flat at `x`, and global sections
  `f₁, …, f_r` of `X` map to a regular sequence in the local ring of the fibre at `x`, then there
  is an open immersion `j : D ⟶ X` from an affine scheme whose image contains `x` such that the
  zero scheme of `j^* f₁, …, j^* f_r` in `D` is flat and locally of finite presentation over `S`.

## References

* [Stacks Project, Tag 06LI](https://stacks.math.columbia.edu/tag/06LI)
* [Stacks Project, Tag 06LW](https://stacks.math.columbia.edu/tag/06LW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

namespace Stacks.AlgebraicGeometry

universe u

/-- **Stacks 06LI for global sections.** Let `g : X ⟶ S` be locally of finite presentation and
flat at `x`, and let `f₁, …, f_r ∈ Γ(X, 𝒪_X)` map to a regular sequence in the local ring of the
fibre `X_{g x}` at `x`.  Then there is an open immersion `j : D ⟶ X` from an affine scheme whose
image contains `x` such that the zero scheme `V(j^* f₁, …, j^* f_r) ⊆ D` is flat and locally of
finite presentation over `S`. -/
theorem exists_affine_openImmersion_flat_zeroScheme_of_isRegular_fiber
    {X S : Scheme.{u}} (g : X ⟶ S) [LocallyOfFinitePresentation g] (x : X) {r : ℕ}
    (f : Fin r → Γ(X, ⊤)) (hflat : IsFlatAt g.toLRSHom.toShHom x)
    (hregular : RingTheory.Sequence.IsRegular
      ((g.fiber (g x)).presheaf.stalk (g.asFiber x))
      (List.ofFn fun i : Fin r =>
        ((g.fiberι (g x)).stalkMap (g.asFiber x)).hom
          ((g.fiberι_asFiber x).symm ▸ X.presheaf.germ ⊤ x trivial (f i)))) :
    ∃ (D : Scheme.{u}) (j : D ⟶ X), IsOpenImmersion j ∧ IsAffine D ∧ x ∈ Set.range j ∧
      Flat ((Scheme.IdealSheafData.ofIdealTop
          (Ideal.ofList (List.ofFn fun i => j.appTop (f i)))).subschemeι ≫ j ≫ g) ∧
      LocallyOfFinitePresentation ((Scheme.IdealSheafData.ofIdealTop
          (Ideal.ofList (List.ofFn fun i => j.appTop (f i)))).subschemeι ≫ j ≫ g) := by
  obtain ⟨U, hx, a, hgerm, -, -, hfl, hfp, -⟩ :=
    exists_affineOpen_regularImmersion_flat_of_isRegular_fiber g x
      (fun i => X.presheaf.germ ⊤ x trivial (f i)) hflat hregular
  have : IsAffine U.1.toScheme := U.2
  set y : U.1.toScheme := ⟨x, hx⟩ with hy
  have hg : ∀ i, U.1.toScheme.presheaf.germ ⊤ y trivial (a i) =
      U.1.toScheme.presheaf.germ ⊤ y trivial (U.1.ι.appTop (f i)) := fun i =>
    (hgerm i).symm.trans (Scheme.Hom.germ_stalkMap_apply U.1.ι ⊤ y trivial (f i))
  choose W hW iU iV heq using fun i =>
    TopCat.Presheaf.germ_eq U.1.toScheme.presheaf (U := ⊤) (V := ⊤) y trivial trivial _ _ (hg i)
  obtain ⟨_, ⟨D₀, hD, rfl⟩, hyD, hDW⟩ :=
    U.1.toScheme.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_iInter.2 hW)
      (isOpen_iInter_of_finite fun i => (W i).2)
  let D : U.1.toScheme.Opens := D₀
  have : IsAffine D.toScheme := hD
  have hres : ∀ i, D.ι.appTop (a i) = D.ι.appTop (U.1.ι.appTop (f i)) := by
    intro i
    have hle : D.ι ''ᵁ ⊤ ≤ W i := by
      rw [Scheme.Opens.ι_image_top]
      exact fun z hz => Set.mem_iInter.1 (hDW hz) i
    have h1 := heq i
    rw [Subsingleton.elim (iU i) (iV i)] at h1
    rw [Scheme.Opens.ι_appTop]
    have hcomp : (homOfLE (le_top : D.ι ''ᵁ ⊤ ≤ ⊤)) = homOfLE hle ≫ iV i := rfl
    rw [hcomp, op_comp, Functor.map_comp]
    exact congrArg (fun t => (U.1.toScheme.presheaf.map (homOfLE hle).op).hom t) h1
  refine ⟨D.toScheme, D.ι ≫ U.1.ι, inferInstance, hD, ⟨⟨y, hyD⟩, rfl⟩, ?_⟩
  have hideal : Ideal.ofList (List.ofFn fun i => (D.ι ≫ U.1.ι).appTop (f i)) =
      Ideal.map D.ι.appTop.hom (Ideal.ofList (List.ofFn a)) := by
    rw [Ideal.map_ofList, List.map_ofFn]
    congr 1
    refine List.ofFn_inj.2 (funext fun i => ?_)
    simp only [Function.comp_apply, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    exact (hres i).symm
  set I := Scheme.IdealSheafData.ofIdealTop (Ideal.ofList (List.ofFn a)) with hI
  have hcomap : I.comap D.ι = Scheme.IdealSheafData.ofIdealTop
      (Ideal.ofList (List.ofFn fun i => (D.ι ≫ U.1.ι).appTop (f i))) := by
    rw [hideal, hI, comap_ofIdealTop]
  rw [← hcomap, Category.assoc]
  have : Flat (I.subschemeι ≫ U.1.ι ≫ g) := hfl
  have : LocallyOfFinitePresentation (I.subschemeι ≫ U.1.ι ≫ g) := hfp
  refine ⟨flat_comap_of_isOpenImmersion I (U.1.ι ≫ g) D.ι, ?_⟩
  have he : (I.comap D.ι).subschemeι ≫ D.ι ≫ U.1.ι ≫ g =
      (I.comapIso D.ι).hom ≫ pullback.snd D.ι I.subschemeι ≫ (I.subschemeι ≫ U.1.ι ≫ g) := by
    simp [← Category.assoc]
  rw [he]
  infer_instance

end Stacks.AlgebraicGeometry

end
