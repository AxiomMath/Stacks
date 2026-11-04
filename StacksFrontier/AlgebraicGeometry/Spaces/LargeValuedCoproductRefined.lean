module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Representable
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringRestrictionFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedCoproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedEtaleAtlas
public import StacksFrontier.CategoryTheory.Sites.CoproductUniversality

/-!
# A coproduct of algebraic spaces, in an arbitrary value universe: the refined forms

Strengthened and additional declarations that belong with
`StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedCoproduct`. A declaration of that module whose
statement was strengthened keeps its original statement there; its strengthened form lives here
under a primed name.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe w v u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Descent of a coproduct cofan to the value universe of the site -/

/-- **A coproduct cofan of algebraic spaces over `S` descends to the value universe of the
site.** Its members and its point are pointwise `u`-small, hence universe lifts of presheaves
of `Type u`, and the shrunk family is again a coproduct cofan, of sheaves of `Type u`.

The algebraic-space condition is unchanged by the lift
(`AlgebraicGeometry.Space.isAlgebraicSpaceULift_comp_uliftFunctor_iff`). The universal property
is not automatic, the category of sheaves of `Type u` on this site not being known to have
coproducts at all: it is transported along the fully faithful lift, a cofan of sheaves of
`Type u` being lifted to one of sheaves of `Type (max w u)`, where the hypothesis applies, and
the resulting morphism brought back down by fullness. No coproduct of sheaves of `Type u` is
formed.

This is the form in which the descent is consumed: the shrunk cofan is presented exactly as
`AlgebraicGeometry.isAlgebraicSpace_coproduct` and
`AlgebraicGeometry.coproductIncl_isOpenImmersion` take it, and the last clause identifies the
lift of each shrunk leg with the given one. -/
theorem exists_shrink_isColimit_cofan {I : Type v} [Small.{u} I]
    {Fᵢ : I → Sheaf (BigFppfOver.topology B S hS) (Type (max w u))}
    (hFᵢ : ∀ i, IsAlgebraicSpaceULift.{w} B S hS (Fᵢ i).obj)
    {G : Sheaf (BigFppfOver.topology B S hS) (Type (max w u))} (ι : ∀ i, Fᵢ i ⟶ G)
    (hG : IsColimit (Cofan.mk G ι)) :
    ∃ (F' : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
      (hF' : ∀ i, IsAlgebraicSpace B S hS (F' i))
      (Gsh : Sheaf (BigFppfOver.topology B S hS) (Type u))
      (ι' : ∀ i, (⟨F' i, (hF' i).isSheaf⟩ :
        Sheaf (BigFppfOver.topology B S hS) (Type u)) ⟶ Gsh)
      (eF : ∀ i, F' i ⋙ uliftFunctor.{w} ≅ (Fᵢ i).obj)
      (eG : Gsh.obj ⋙ uliftFunctor.{w} ≅ G.obj),
      Nonempty (IsColimit (Cofan.mk Gsh ι')) ∧
        ∀ i, Functor.whiskerRight (ι' i).hom uliftFunctor.{w} =
          (eF i).hom ≫ (ι i).hom ≫ eG.inv := by
  let J := BigFppfOver.topology B S hS
  let C := BigFppfOver B S hS
  let H := (Functor.whiskeringRight Cᵒᵖ (Type u) (Type (max w u))).obj uliftFunctor.{w}
  let _ : FunctorToTypes.Small.{u} G.obj := small_of_isColimit_cofan B S hS hFᵢ ι hG
  let _ : ∀ i, FunctorToTypes.Small.{u} (Fᵢ i).obj := fun i =>
    small_of_isAlgebraicSpaceULift B S hS (hFᵢ i)
  let G' : Cᵒᵖ ⥤ Type u := FunctorToTypes.shrink.{u} G.obj
  let F' : I → (Cᵒᵖ ⥤ Type u) := fun i => FunctorToTypes.shrink.{u} (Fᵢ i).obj
  let eG : H.obj G' ≅ G.obj := shrinkCompUliftFunctorIso G.obj
  let eF : ∀ i, H.obj (F' i) ≅ (Fᵢ i).obj := fun i => shrinkCompUliftFunctorIso (Fᵢ i).obj
  -- the algebraic-space condition descends to the value universe of the site
  have hF'alg : ∀ i, IsAlgebraicSpace B S hS (F' i) := fun i =>
    (isAlgebraicSpaceULift_comp_uliftFunctor_iff B S hS (F' i)).mp
      (isAlgebraicSpaceULift_of_iso B S hS (eF i).symm (hFᵢ i))
  have hG'sheaf : Presheaf.IsSheaf J G' := by
    have h1 : Presheaf.IsSheaf J (G' ⋙ uliftFunctor.{w}) :=
      (Presheaf.isSheaf_of_iso_iff eG).mpr G.property
    simpa only [isSheaf_iff_isSheaf_of_type, Presieve.isSheaf_comp_uliftFunctor_iff] using h1
  let Gsh : Sheaf J (Type u) := ⟨G', hG'sheaf⟩
  let Fsh : I → Sheaf J (Type u) := fun i => ⟨F' i, (hF'alg i).isSheaf⟩
  let ι' : ∀ i, F' i ⟶ G' := fun i => H.preimage ((eF i).hom ≫ (ι i).hom ≫ eG.inv)
  have hmapι' : ∀ i, H.map (ι' i) = (eF i).hom ≫ (ι i).hom ≫ eG.inv := fun i =>
    H.map_preimage _
  let ιsh : ∀ i, Fsh i ⟶ Gsh := fun i => ObjectProperty.homMk (ι' i)
  -- the universe lift of a sheaf of `Type u`
  let lift : Sheaf J (Type u) → Sheaf J (Type (max w u)) := fun K =>
    ⟨H.obj K.obj, by
      rw [isSheaf_iff_isSheaf_of_type]
      exact (Presieve.isSheaf_comp_uliftFunctor_iff _).mpr
        ((isSheaf_iff_isSheaf_of_type J _).1 K.property)⟩
  let big : ∀ (c : Cofan Fsh) (i : I), Fᵢ i ⟶ lift c.pt := fun c i =>
    ObjectProperty.homMk ((eF i).inv ≫ H.map (c.inj i).hom)
  let desc : ∀ c : Cofan Fsh, Gsh ⟶ c.pt := fun c =>
    ObjectProperty.homMk (H.preimage (eG.hom ≫ (Cofan.IsColimit.desc hG (big c)).hom))
  have hdescmap : ∀ c : Cofan Fsh,
      H.map (desc c).hom = eG.hom ≫ (Cofan.IsColimit.desc hG (big c)).hom := fun c =>
    H.map_preimage _
  have hbig : ∀ (c : Cofan Fsh) (i : I),
      (ι i).hom ≫ (Cofan.IsColimit.desc hG (big c)).hom =
        (eF i).inv ≫ H.map (c.inj i).hom := fun c i =>
    congrArg (fun k : Fᵢ i ⟶ lift c.pt => k.hom) (Cofan.IsColimit.fac hG (big c) i)
  -- the shrunk cofan is a coproduct, by fullness of the lift
  have hGcolim : IsColimit (Cofan.mk Gsh ιsh) := by
    refine Cofan.IsColimit.mk _ desc (fun c i => ?_) (fun c m hm => ?_)
    · refine Sheaf.hom_ext ?_
      show ι' i ≫ (desc c).hom = (c.inj i).hom
      apply H.map_injective
      rw [Functor.map_comp, hmapι', hdescmap]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [hbig]
      simp
    · have hmi : ∀ i, ι' i ≫ m.hom = (c.inj i).hom := fun i =>
        congrArg (fun k : Fsh i ⟶ c.pt => k.hom) (hm i)
      have hψ : (ObjectProperty.homMk (eG.inv ≫ H.map m.hom) : G ⟶ lift c.pt)
          = Cofan.IsColimit.desc hG (big c) := by
        refine Cofan.IsColimit.hom_ext hG _ _ fun i => ?_
        refine Sheaf.hom_ext ?_
        show (ι i).hom ≫ eG.inv ≫ H.map m.hom =
          (ι i).hom ≫ (Cofan.IsColimit.desc hG (big c)).hom
        have h3 : (eF i).hom ≫ (ι i).hom ≫ eG.inv ≫ H.map m.hom =
            H.map (c.inj i).hom := by
          have h4 := congrArg H.map (hmi i)
          rw [Functor.map_comp, hmapι'] at h4
          simpa only [Category.assoc] using h4
        rw [hbig, ← h3, Iso.inv_hom_id_assoc]
      refine Sheaf.hom_ext ?_
      show m.hom = (desc c).hom
      apply H.map_injective
      rw [hdescmap, ← congrArg (fun k : G ⟶ lift c.pt => k.hom) hψ]
      show _ = eG.hom ≫ eG.inv ≫ H.map m.hom
      rw [Iso.hom_inv_id_assoc]
  exact ⟨F', hF'alg, Gsh, ιsh, eF, eG, ⟨hGcolim⟩, hmapι'⟩

/-! ### Stacks 02WQ in an arbitrary value universe -/

end AlgebraicGeometry.Space

end
