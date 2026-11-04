module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionULiftTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedCoproductRefined
public import StacksFrontier.CategoryTheory.Sites.InfinitaryExtensive

/-!
# Completion commutes with coproducts of algebraic spaces

Let `V = ∐ᵢ Vᵢ` be a coproduct of algebraic spaces over `S`, formed among fppf sheaves of
`Type u` and indexed by a `u`-small type, and let `q : V ⟶ X` be a morphism to a presheaf `X`
with a set `T` of points. Then the completion `V_{/q⁻¹T}` is the coproduct, among fppf sheaves of
`Type (u + 1)`, of the completions of the `Vᵢ` along the inverse images of `T`.

The universe lift `V ⋙ ULift` is the coproduct of the `Vᵢ ⋙ ULift`: the coproduct of the
universe lifts descends to the value universe of the site
(`AlgebraicGeometry.Space.exists_shrink_isColimit_cofan`), where it is identified with `V` by
uniqueness of colimits. The completion is the base change of the sheafified universe lift along
`X_{/T} ⟶ X` (Stacks 0APV), and coproducts of sheaves of sets are universal.

## Main results

* `AlgebraicGeometry.Space.nonempty_isColimit_cofan_sheafifiedULift`: the sheafified universe
  lift of a coproduct of algebraic spaces is the coproduct of the sheafified universe lifts.
* `AlgebraicGeometry.Space.nonempty_isColimit_cofan_completionSheaf`: the completion of a
  coproduct of algebraic spaces is the coproduct of the completions.

## References

* [Stacks Project, Tag 0APV](https://stacks.math.columbia.edu/tag/0APV)
* [Stacks Project, Tag 0AMC](https://stacks.math.columbia.edu/tag/0AMC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The universe lift of a coproduct of algebraic spaces is a coproduct.** For a coproduct
`V = ∐ᵢ Aᵢ` of algebraic spaces among fppf sheaves of `Type u`, indexed by a `u`-small type,
the universe lift `V ⋙ ULift` is the coproduct of the `Aᵢ ⋙ ULift` among fppf sheaves of
`Type (u + 1)`. -/
theorem nonempty_isColimit_cofan_uliftFunctor {ι : Type u}
    {A : ι → Sheaf (BigFppfOver.topology B S hS) (Type u)}
    (hA : ∀ i, IsAlgebraicSpace B S hS (A i).obj)
    {V : Sheaf (BigFppfOver.topology B S hS) (Type u)} (ιV : ∀ i, A i ⟶ V)
    (hV : IsColimit (Cofan.mk V ιV)) :
    Nonempty (IsColimit (Cofan.mk
      ((sheafCompose (BigFppfOver.topology B S hS) uliftFunctor.{u + 1, u}).obj V)
      (fun i ↦
        (sheafCompose (BigFppfOver.topology B S hS) uliftFunctor.{u + 1, u}).map (ιV i)))) := by
  let J := BigFppfOver.topology B S hS
  let L := sheafCompose J uliftFunctor.{u + 1, u}
  let : HasColimitsOfSize.{u + 1, u + 1} (Sheaf J (Type (u + 1))) := Sheaf.instHasColimitsOfSize
  let : HasColimitsOfShape (Discrete ι) (Sheaf J (Type (u + 1))) :=
    (hasColimitsOfSizeShrink.{u, u, u + 1, u + 1} _).has_colimits_of_shape _
  let Fi : ι → Sheaf J (Type (max (u + 1) u)) := fun i ↦ L.obj (A i)
  have hFi : ∀ i, IsAlgebraicSpaceULift.{u + 1} B S hS (Fi i).obj := fun i ↦
    (isAlgebraicSpaceULift_comp_uliftFunctor_iff B S hS (A i).obj).2 (hA i)
  obtain ⟨F', hF', Gsh, ι', eF, eG, ⟨hGsh⟩, hcomp⟩ :=
    exists_shrink_isColimit_cofan B S hS hFi (Sigma.ι Fi) (coproductIsCoproduct Fi)
  -- the members of the descended coproduct are the `A i`
  let ff := (fullyFaithfulULiftFunctor.{u + 1, u}).whiskeringRight (BigFppfOver B S hS)ᵒᵖ
  let f : ∀ i, (⟨F' i, (hF' i).isSheaf⟩ : Sheaf J (Type u)) ≅ A i := fun i ↦
    (fullyFaithfulSheafToPresheaf J (Type u)).preimageIso (ff.preimageIso (eF i))
  have hf : ∀ i, Functor.whiskerRight (f i).hom.hom uliftFunctor.{u + 1, u} = (eF i).hom :=
    fun i ↦ ff.map_preimage (eF i).hom
  -- `Gsh ≅ V`, compatibly with the injections
  have hfacV : ∀ {Y : Sheaf J (Type u)} (g : ∀ i, A i ⟶ Y) i,
      ιV i ≫ Cofan.IsColimit.desc hV g = g i := fun g i ↦ Cofan.IsColimit.fac hV g i
  have hV' : IsColimit (Cofan.mk V (fun i ↦ (f i).hom ≫ ιV i)) := by
    refine Cofan.IsColimit.mk _ (fun s ↦ Cofan.IsColimit.desc hV (fun i ↦ (f i).inv ≫ s.inj i))
      (fun s i ↦ ?_) (fun s m hm ↦ Cofan.IsColimit.hom_ext hV _ _ fun i ↦ ?_)
    · show ((f i).hom ≫ ιV i) ≫ _ = _
      rw [Category.assoc, hfacV, Iso.hom_inv_id_assoc]
    · show ιV i ≫ _ = ιV i ≫ _
      rw [hfacV, ← hm i]
      show ιV i ≫ m = (f i).inv ≫ ((f i).hom ≫ ιV i) ≫ m
      rw [Category.assoc, Iso.inv_hom_id_assoc]
  let θ : Gsh ≅ V := hGsh.coconePointUniqueUpToIso hV'
  have hθ : ∀ i, ι' i ≫ θ.hom = (f i).hom ≫ ιV i := fun i ↦
    hGsh.comp_coconePointUniqueUpToIso_hom hV' ⟨i⟩
  -- the identification of `V ⋙ ULift` with the coproduct of the universe lifts
  let E : L.obj V ≅ ∐ Fi := (fullyFaithfulSheafToPresheaf J (Type (u + 1))).preimageIso
    (Functor.isoWhiskerRight ((sheafToPresheaf J (Type u)).mapIso θ.symm)
      uliftFunctor.{u + 1, u} ≪≫ eG)
  have hE : ∀ i, L.map (ιV i) ≫ E.hom = Sigma.ι Fi i := by
    intro i
    have h1 : ιV i ≫ θ.inv = (f i).inv ≫ ι' i := by
      rw [Iso.comp_inv_eq, Category.assoc, hθ, Iso.inv_hom_id_assoc]
    have h2 : Functor.whiskerRight (f i).inv.hom uliftFunctor.{u + 1, u} ≫ (eF i).hom = 𝟙 _ := by
      have hf' : Functor.whiskerRight (f i).inv.hom uliftFunctor.{u + 1, u} = (eF i).inv :=
        ff.map_preimage (eF i).inv
      rw [hf']
      exact (eF i).inv_hom_id
    apply (sheafToPresheaf J (Type (u + 1))).map_injective
    show Functor.whiskerRight (ιV i).hom uliftFunctor.{u + 1, u} ≫
      (Functor.whiskerRight θ.inv.hom uliftFunctor.{u + 1, u} ≫ eG.hom) = (Sigma.ι Fi i).hom
    rw [← Category.assoc, ← Functor.whiskerRight_comp]
    show Functor.whiskerRight (ιV i ≫ θ.inv).hom uliftFunctor.{u + 1, u} ≫ eG.hom = _
    rw [h1]
    show Functor.whiskerRight ((f i).inv.hom ≫ (ι' i).hom) uliftFunctor.{u + 1, u} ≫ eG.hom = _
    rw [Functor.whiskerRight_comp, hcomp i, Category.assoc, Category.assoc, Category.assoc,
      Iso.inv_hom_id, Category.comp_id, ← Category.assoc, h2]
    exact Category.id_comp _
  exact ⟨IsColimit.ofIsoColimit (coproductIsCoproduct Fi)
    (Cofan.ext E.symm fun i ↦ by rw [Iso.symm_hom, Iso.comp_inv_eq]; exact (hE i).symm)⟩

/-- **The sheafified universe lift of a coproduct of algebraic spaces is a coproduct.** -/
theorem nonempty_isColimit_cofan_sheafifiedULift {ι : Type u}
    {A : ι → Sheaf (BigFppfOver.topology B S hS) (Type u)}
    (hA : ∀ i, IsAlgebraicSpace B S hS (A i).obj)
    {V : Sheaf (BigFppfOver.topology B S hS) (Type u)} (ιV : ∀ i, A i ⟶ V)
    (hV : IsColimit (Cofan.mk V ιV)) :
    Nonempty (IsColimit (Cofan.mk (sheafifiedULift B S hS V.obj)
      (fun i ↦ sheafifiedULiftMap B S hS (ιV i).hom))) := by
  let J := BigFppfOver.topology B S hS
  obtain ⟨hL⟩ := nonempty_isColimit_cofan_uliftFunctor hA ιV hV
  let e : ∀ Y : Sheaf J (Type u),
      (sheafCompose J uliftFunctor.{u + 1, u}).obj Y ≅ sheafifiedULift B S hS Y.obj := fun Y ↦
    (fullyFaithfulSheafToPresheaf J (Type (u + 1))).preimageIso
      (sheafifiedULiftIso B S hS Y.obj Y.property)
  have he : ∀ i, sheafifiedULiftMap B S hS (ιV i).hom ≫ (e V).inv =
      (e (A i)).inv ≫ (sheafCompose J uliftFunctor.{u + 1, u}).map (ιV i) := by
    intro i
    rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
    apply (sheafToPresheaf J (Type (u + 1))).map_injective
    show (sheafifiedULiftIso B S hS (A i).obj (A i).property).hom ≫
        (sheafifiedULiftMap B S hS (ιV i).hom).hom =
      Functor.whiskerRight (ιV i).hom uliftFunctor.{u + 1, u} ≫
        (sheafifiedULiftIso B S hS V.obj V.property).hom
    exact (whiskerRight_comp_sheafifiedULiftIso_hom B S hS (A i).property V.property _).symm
  have hfacL : ∀ {Y : Sheaf J (Type (u + 1))}
      (g : ∀ i, (sheafCompose J uliftFunctor.{u + 1, u}).obj (A i) ⟶ Y) i,
      (sheafCompose J uliftFunctor.{u + 1, u}).map (ιV i) ≫ Cofan.IsColimit.desc hL g = g i :=
    fun g i ↦ Cofan.IsColimit.fac hL g i
  refine ⟨Cofan.IsColimit.mk _
    (fun s ↦ (e V).inv ≫ Cofan.IsColimit.desc hL (fun i ↦ (e (A i)).hom ≫ s.inj i))
    (fun s i ↦ ?_) (fun s m hm ↦ ?_)⟩
  · show sheafifiedULiftMap B S hS (ιV i).hom ≫ _ = _
    rw [← Category.assoc, he, Category.assoc, hfacL, Iso.inv_hom_id_assoc]
  · rw [Iso.eq_inv_comp]
    refine Cofan.IsColimit.hom_ext hL _ _ fun i ↦ ?_
    show (sheafCompose J uliftFunctor.{u + 1, u}).map (ιV i) ≫ _ =
      (sheafCompose J uliftFunctor.{u + 1, u}).map (ιV i) ≫ _
    have he' : (sheafCompose J uliftFunctor.{u + 1, u}).map (ιV i) ≫ (e V).hom =
        (e (A i)).hom ≫ sheafifiedULiftMap B S hS (ιV i).hom := by
      rw [← Iso.inv_comp_eq, ← Category.assoc, ← he, Category.assoc, Iso.inv_hom_id,
        Category.comp_id]
    rw [hfacL, ← hm i, ← Category.assoc, he', Category.assoc]
    rfl

/-- **Completion commutes with coproducts of algebraic spaces.** Let `V = ∐ᵢ Aᵢ` be a coproduct
of algebraic spaces among fppf sheaves of `Type u`, let `q : V ⟶ X` be a morphism to a presheaf
and let `T` be a set of points of `X`. The completion of `V` along `|q|⁻¹ T` is the coproduct
of the completions of the `Aᵢ` along the inverse images, with the completed injections.

The completion is the base change of the sheafified universe lift along the inclusion of the
completion (Stacks 0APV), the sheafified universe lift of `V` is the coproduct of those of the
`Aᵢ` (`nonempty_isColimit_cofan_sheafifiedULift`), and coproducts of sheaves of sets are
universal. -/
theorem nonempty_isColimit_cofan_completionSheaf {ι : Type u}
    {A : ι → Sheaf (BigFppfOver.topology B S hS) (Type u)}
    (hA : ∀ i, IsAlgebraicSpace B S hS (A i).obj)
    {V : Sheaf (BigFppfOver.topology B S hS) (Type u)} (ιV : ∀ i, A i ⟶ V)
    (hV : IsColimit (Cofan.mk V ιV)) {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (q : V.obj ⟶ X)
    (T : Set (points B S hS X)) :
    Nonempty (IsColimit (Cofan.mk (completionSheaf B S hS V.obj (pointsMap B S hS _ q ⁻¹' T))
      (fun i ↦ completionSheafMap B S hS (ιV i).hom (pointsMap B S hS _ q ⁻¹' T)))) := by
  obtain ⟨hU⟩ := nonempty_isColimit_cofan_sheafifiedULift hA ιV hV
  exact Sheaf.nonempty_isColimit_cofanMk_of_isPullback (BigFppfOver.topology B S hS)
    (fun i ↦ sheafifiedULiftMap B S hS (ιV i).hom) hU
    (completionSheafInclusion B S hS V.obj (pointsMap B S hS _ q ⁻¹' T))
    (fun i ↦ completionSheafMap B S hS (ιV i).hom (pointsMap B S hS _ q ⁻¹' T))
    (fun i ↦ completionSheafInclusion B S hS (A i).obj _)
    (fun i ↦ (isPullback_completionSheafMap B S hS (ιV i).hom _).flip)

end AlgebraicGeometry.Space

end
