module

public import StacksFrontier.CategoryTheory.Functor.TransportBifunctorComparison
public import StacksFrontier.CategoryTheory.Shift.DetectingCommShift
public import StacksFrontier.CategoryTheory.Shift.CommShiftTwoPrecompIso
public import StacksFrontier.CategoryTheory.Shift.CommShiftTwoDataTransport
public import StacksFrontier.CategoryTheory.Shift.CommShiftTwoOfIso

/-!
# A transported comparison of bifunctors commutes with the shift

In the setting of `CategoryTheory.Functor.transportBifunctorComparison`, let all categories carry
shifts by `A` and all functors and isomorphisms be compatible with them, in the first variable of
the bifunctors. If the comparison `δs : L_s(T_s(K, L)) ⟶ T'_s(L_s K, L_s L)` commutes with the
shift in `K`, and a natural comparison `δl` agrees with the transport of `δs` at all images under
an essentially surjective `G_C`, then `δl` commutes with the shift in `K` too, at every fixed
second argument.

## Main definitions

* `CategoryTheory.Functor.bifunctorComparisonFlip`: a comparison of bifunctors at a fixed second
  argument, as a morphism of functors of the first.

## Main results

* `CategoryTheory.Functor.commShift_bifunctorComparisonFlip_of_iso`: its shift compatibility only
  depends on the second argument up to isomorphism.
* `CategoryTheory.Functor.commShift_of_eq_transportBifunctorComparison`: a comparison agreeing
  with a transported one commutes with the shift in its first variable.
* `CategoryTheory.Functor.commShift_of_eq_transportBifunctorComparisonInt`: the same for
  bifunctors commuting with the shifts by `ℤ` in both variables, with the transporting
  isomorphisms of bifunctors compatible with the shift in the first variable for the data
  `CategoryTheory.Functor.CommShift₂.precomp₁`, `precomp₂` and `postcompInt`.
-/

@[expose] public section

open CategoryTheory
open scoped CategoryTheory.Prod

namespace CategoryTheory.Functor

variable {Cs Cl Ds Dl : Type*} [Category Cs] [Category Cl] [Category Ds] [Category Dl]
  {A : Type*} [AddMonoid A] [HasShift Cs A] [HasShift Cl A] [HasShift Ds A] [HasShift Dl A]
  (GC : Cs ⥤ Cl) (GD : Ds ⥤ Dl) {Ts : Cs ⥤ Cs ⥤ Cs} {Tl : Cl ⥤ Cl ⥤ Cl}
  {Ts' : Ds ⥤ Ds ⥤ Ds} {Tl' : Dl ⥤ Dl ⥤ Dl} {Ls : Cs ⥤ Ds} {Ll : Cl ⥤ Dl}
  (pb : Ls ⋙ GD ≅ GC ⋙ Ll)
  (τC : GC ⋙ Tl ⋙ (whiskeringLeft _ _ _).obj GC ≅ Ts ⋙ (whiskeringRight _ _ _).obj GC)
  (τD : GD ⋙ Tl' ⋙ (whiskeringLeft _ _ _).obj GD ≅ Ts' ⋙ (whiskeringRight _ _ _).obj GD)
  (δs : uncurry.obj Ts ⋙ Ls ⟶ Ls.prod Ls ⋙ uncurry.obj Ts')
  [GC.CommShift A] [GD.CommShift A] [Ls.CommShift A] [Ll.CommShift A]
  [∀ L, (Ts.flip.obj L).CommShift A] [∀ L, (Tl.flip.obj L).CommShift A]
  [∀ L, (Ts'.flip.obj L).CommShift A] [∀ L, (Tl'.flip.obj L).CommShift A]

/-- The comparison `δs` at a fixed second argument `L`, as a morphism of functors of the first
argument. -/
@[simps]
def bifunctorComparisonFlip (L : Cs) : Ts.flip.obj L ⋙ Ls ⟶ Ls ⋙ Ts'.flip.obj (Ls.obj L) where
  app K := δs.app (K, L)
  naturality {K K'} u := by
    have := δs.naturality (u ×ₘ 𝟙 L)
    simpa using this

/-- A first-variable comparison at `L` commutes with the shift if it is conjugate, by the images
of an isomorphism `L ≅ L'`, to one at `L'` which does. -/
private theorem commShift_flip_of_conj {C D : Type*} [Category C] [Category D] [HasShift C A]
    [HasShift D A] {F : C ⥤ D} [F.CommShift A] {T : C ⥤ C ⥤ C} {T' : D ⥤ D ⥤ D}
    [∀ L, (T.flip.obj L).CommShift A] [∀ L, (T'.flip.obj L).CommShift A]
    [∀ {L L' : C} (g : L ⟶ L'), NatTrans.CommShift (T.flip.map g) A]
    [∀ {L L' : D} (g : L ⟶ L'), NatTrans.CommShift (T'.flip.map g) A] {L L' : C} (e : L ≅ L')
    (σ : T.flip.obj L ⋙ F ⟶ F ⋙ T'.flip.obj (F.obj L))
    (σ' : T.flip.obj L' ⋙ F ⟶ F ⋙ T'.flip.obj (F.obj L')) [NatTrans.CommShift σ' A]
    (h : ∀ K, σ.app K =
      F.map ((T.obj K).map e.hom) ≫ σ'.app K ≫ (T'.obj (F.obj K)).map (F.map e.inv)) :
    NatTrans.CommShift σ A := by
  have : NatTrans.CommShift (isoWhiskerRight (T.flip.mapIso e) F).hom A :=
    inferInstanceAs (NatTrans.CommShift (whiskerRight (T.flip.map e.hom) F) A)
  have : NatTrans.CommShift (isoWhiskerLeft F (T'.flip.mapIso (F.mapIso e))).hom A :=
    inferInstanceAs (NatTrans.CommShift (whiskerLeft F (T'.flip.map (F.map e.hom))) A)
  exact NatTrans.commShift_of_eq_conj (isoWhiskerRight (T.flip.mapIso e) F)
    (isoWhiskerLeft F (T'.flip.mapIso (F.mapIso e))) σ' (by ext K; exact h K)

/-- **The first-variable component of a comparison of bifunctors only depends on the fixed second
argument up to isomorphism**: the components at isomorphic objects are conjugate by the images of
the isomorphism under the two bifunctors, which commute with the shift. -/
theorem commShift_bifunctorComparisonFlip_of_iso
    [∀ {L L' : Cs} (g : L ⟶ L'), NatTrans.CommShift (Ts.flip.map g) A]
    [∀ {L L' : Ds} (g : L ⟶ L'), NatTrans.CommShift (Ts'.flip.map g) A] {L L' : Cs} (e : L ≅ L')
    (h : NatTrans.CommShift (bifunctorComparisonFlip δs L') A) :
    NatTrans.CommShift (bifunctorComparisonFlip δs L) A := by
  refine commShift_flip_of_conj e _ (bifunctorComparisonFlip δs L') (fun K => ?_)
  have := δs.naturality (𝟙 K ×ₘ e.hom)
  simp only [Functor.comp_map, uncurry_obj_map, Functor.map_id, NatTrans.id_app,
    Category.id_comp, Functor.prod_map] at this
  change δs.app (K, L) = Ls.map ((Ts.obj K).map e.hom) ≫ δs.app (K, L') ≫
    (Ts'.obj (Ls.obj K)).map (Ls.map e.inv)
  rw [reassoc_of% this]
  simp only [Functor.prod_obj, Functor.map_id, NatTrans.id_app]
  rw [← Functor.map_comp, ← Functor.map_comp, Iso.hom_inv_id, Functor.map_id, Functor.map_id]
  simp

/-- The first-variable component at `L` of the transported comparison, as a morphism of
functors of `K` restricted along `G_C`, written as a composite of whiskerings. -/
def transportBifunctorComparisonFlipApp (L : Cs) :
    GC ⋙ (Tl.flip.obj (GC.obj L) ⋙ Ll) ⟶ GC ⋙ (Ll ⋙ Tl'.flip.obj (Ll.obj (GC.obj L))) :=
  (Functor.associator _ _ _).inv ≫
    whiskerRight (show GC ⋙ Tl.flip.obj (GC.obj L) ⟶ Ts.flip.obj L ⋙ GC from τC.hom.flipApp L) Ll ≫
    (Functor.associator _ _ _).hom ≫ whiskerLeft (Ts.flip.obj L) pb.inv ≫
    (Functor.associator _ _ _).inv ≫
    whiskerRight (bifunctorComparisonFlip δs L) GD ≫
    (Functor.associator _ _ _).hom ≫
    whiskerLeft Ls (show Ts'.flip.obj (Ls.obj L) ⋙ GD ⟶ GD ⋙ Tl'.flip.obj (GD.obj (Ls.obj L))
      from τD.inv.flipApp (Ls.obj L)) ≫
    (Functor.associator _ _ _).inv ≫
    whiskerRight pb.hom (Tl'.flip.obj (GD.obj (Ls.obj L))) ≫
    whiskerLeft (GC ⋙ Ll) (Tl'.flip.map (pb.hom.app L)) ≫ (Functor.associator _ _ _).hom

/-- The component at `K` of `transportBifunctorComparisonFlipApp` at `L` is the transported
comparison `transportBifunctorComparison` at `(K, L)`. -/
theorem transportBifunctorComparisonFlipApp_app (L K : Cs) :
    (transportBifunctorComparisonFlipApp GC GD pb τC τD δs L).app K =
      transportBifunctorComparison GC GD pb τC τD δs K L := by
  simp [transportBifunctorComparisonFlipApp, transportBifunctorComparison]

/-- The first-variable component of the transported comparison commutes with the shift. -/
theorem commShift_transportBifunctorComparisonFlipApp (L : Cs)
    [∀ {L L' : Dl} (g : L ⟶ L'), NatTrans.CommShift (Tl'.flip.map g) A]
    [NatTrans.CommShift pb.hom A]
    (hτC : NatTrans.CommShift
      (show GC ⋙ Tl.flip.obj (GC.obj L) ⟶ Ts.flip.obj L ⋙ GC from τC.hom.flipApp L) A)
    (hτD : NatTrans.CommShift
      (show Ts'.flip.obj (Ls.obj L) ⋙ GD ⟶ GD ⋙ Tl'.flip.obj (GD.obj (Ls.obj L)) from
        τD.inv.flipApp (Ls.obj L)) A)
    (hδs : NatTrans.CommShift
      (bifunctorComparisonFlip δs L) A) :
    NatTrans.CommShift (transportBifunctorComparisonFlipApp GC GD pb τC τD δs L) A := by
  unfold transportBifunctorComparisonFlipApp
  infer_instance

/-- **A comparison agreeing with a transported one commutes with the shift in its first
variable** as soon as the transported comparison and every transporting isomorphism do, and
`G_C` is essentially surjective. -/
theorem commShift_of_eq_transportBifunctorComparison [GC.EssSurj]
    [∀ {L L' : Dl} (g : L ⟶ L'), NatTrans.CommShift (Tl'.flip.map g) A]
    [∀ {L L' : Cl} (g : L ⟶ L'), NatTrans.CommShift (Tl.flip.map g) A]
    [NatTrans.CommShift pb.hom A]
    (hτC : ∀ L, NatTrans.CommShift
      (show GC ⋙ Tl.flip.obj (GC.obj L) ⟶ Ts.flip.obj L ⋙ GC from τC.hom.flipApp L) A)
    (hτD : ∀ L, NatTrans.CommShift (show Ts'.flip.obj L ⋙ GD ⟶ GD ⋙ Tl'.flip.obj (GD.obj L) from
      τD.inv.flipApp L) A)
    (hδs : ∀ L, NatTrans.CommShift
      (bifunctorComparisonFlip δs L) A)
    (δl : ∀ K L : Cl, Ll.obj ((Tl.obj K).obj L) ⟶ (Tl'.obj (Ll.obj K)).obj (Ll.obj L))
    (hδl : ∀ {K K' L L' : Cl} (u : K ⟶ K') (v : L ⟶ L'),
      Ll.map ((Tl.map u).app _ ≫ (Tl.obj _).map v) ≫ δl K' L' =
        δl K L ≫ (Tl'.map (Ll.map u)).app _ ≫ (Tl'.obj _).map (Ll.map v))
    (h : ∀ K L, δl (GC.obj K) (GC.obj L) = transportBifunctorComparison GC GD pb τC τD δs K L)
    (M : Cl) (σ : Tl.flip.obj M ⋙ Ll ⟶ Ll ⋙ Tl'.flip.obj (Ll.obj M))
    (hσ : ∀ K, σ.app K = δl K M) :
    NatTrans.CommShift σ A := by
  obtain ⟨L, ⟨e⟩⟩ : ∃ L, Nonempty (GC.obj L ≅ M) := ⟨_, ⟨GC.objObjPreimageIso M⟩⟩
  let σ' : Tl.flip.obj (GC.obj L) ⋙ Ll ⟶ Ll ⋙ Tl'.flip.obj (Ll.obj (GC.obj L)) :=
    { app := fun K => δl K (GC.obj L)
      naturality := fun {K K'} u => by
        have := hδl u (𝟙 (GC.obj L))
        simp only [Functor.map_id, Category.comp_id] at this
        simpa using this }
  have hσ' : NatTrans.CommShift σ' A := by
    refine NatTrans.commShift_of_whiskerLeft GC σ' ?_
    have := commShift_transportBifunctorComparisonFlipApp GC GD pb τC τD δs L (hτC L)
      (hτD (Ls.obj L)) (hδs L)
    refine NatTrans.commShift_of_eq (θ := transportBifunctorComparisonFlipApp GC GD pb τC τD δs L)
      ?_
    ext K
    exact (h K L).trans (transportBifunctorComparisonFlipApp_app GC GD pb τC τD δs L K).symm
  refine commShift_flip_of_conj e.symm _ σ' (fun K => ?_)
  have := hδl (𝟙 K) e.inv
  simp only [Functor.map_id, NatTrans.id_app, Category.id_comp] at this
  change σ.app K = Ll.map ((Tl.obj K).map e.inv) ≫ δl K (GC.obj L) ≫
    (Tl'.obj (Ll.obj K)).map (Ll.map e.hom)
  rw [reassoc_of% this, hσ, ← Functor.map_comp, ← Functor.map_comp, Iso.inv_hom_id,
    Functor.map_id, Functor.map_id, Category.comp_id]

section Int

variable {Cs Cl Ds Dl : Type*} [Category Cs] [Category Cl] [Category Ds] [Category Dl]
  [Preadditive Cs] [Preadditive Cl] [Preadditive Ds] [Preadditive Dl]
  [HasShift Cs ℤ] [HasShift Cl ℤ] [HasShift Ds ℤ] [HasShift Dl ℤ]
  [hCs : ∀ n : ℤ, (shiftFunctor Cs n).Additive] [hCl : ∀ n : ℤ, (shiftFunctor Cl n).Additive]
  [hDs : ∀ n : ℤ, (shiftFunctor Ds n).Additive] [hDl : ∀ n : ℤ, (shiftFunctor Dl n).Additive]

/-- **`commShift_of_eq_transportBifunctorComparison` for bifunctors commuting with the shifts by
`ℤ` in both variables.** The transporting isomorphisms of bifunctors are asked to commute with
the shift in the first variable for the data `CategoryTheory.Functor.CommShift₂.precomp₁` after
`precomp₂` on `G ⋙ T ⋙ (- ⋙ G)` and `CategoryTheory.Functor.CommShift₂.postcompInt` on
`T ⋙ (- ⋙ G)`. -/
theorem commShift_of_eq_transportBifunctorComparisonInt
    (GC : Cs ⥤ Cl) (GD : Ds ⥤ Dl) {Ts : Cs ⥤ Cs ⥤ Cs} {Tl : Cl ⥤ Cl ⥤ Cl}
    {Ts' : Ds ⥤ Ds ⥤ Ds} {Tl' : Dl ⥤ Dl ⥤ Dl} {Ls : Cs ⥤ Ds} {Ll : Cl ⥤ Dl}
    (pb : Ls ⋙ GD ≅ GC ⋙ Ll)
    (τC : GC ⋙ Tl ⋙ (whiskeringLeft _ _ _).obj GC ≅ Ts ⋙ (whiskeringRight _ _ _).obj GC)
    (τD : GD ⋙ Tl' ⋙ (whiskeringLeft _ _ _).obj GD ≅ Ts' ⋙ (whiskeringRight _ _ _).obj GD)
    (δs : uncurry.obj Ts ⋙ Ls ⟶ Ls.prod Ls ⋙ uncurry.obj Ts')
    [GC.CommShift ℤ] [GD.CommShift ℤ] [GC.Additive] [GD.Additive] [Ls.CommShift ℤ]
    [Ll.CommShift ℤ] [sTs : Ts.CommShift₂Int] [sTl : Tl.CommShift₂Int] [sTs' : Ts'.CommShift₂Int]
    [sTl' : Tl'.CommShift₂Int] [GC.EssSurj] [NatTrans.CommShift pb.hom ℤ]
    (hτC : ∀ L, NatTrans.CommShift (τC.hom.flipApp L) ℤ)
    (hτD : ∀ L, NatTrans.CommShift (τD.hom.flipApp L) ℤ)
    (hδs : ∀ L, NatTrans.CommShift (bifunctorComparisonFlip δs L) ℤ)
    (δl : ∀ K L : Cl, Ll.obj ((Tl.obj K).obj L) ⟶ (Tl'.obj (Ll.obj K)).obj (Ll.obj L))
    (hδl : ∀ {K K' L L' : Cl} (u : K ⟶ K') (v : L ⟶ L'),
      Ll.map ((Tl.map u).app _ ≫ (Tl.obj _).map v) ≫ δl K' L' =
        δl K L ≫ (Tl'.map (Ll.map u)).app _ ≫ (Tl'.obj _).map (Ll.map v))
    (h : ∀ K L, δl (GC.obj K) (GC.obj L) = transportBifunctorComparison GC GD pb τC τD δs K L)
    (M : Cl) (σ : Tl.flip.obj M ⋙ Ll ⟶ Ll ⋙ Tl'.flip.obj (Ll.obj M))
    (hσ : ∀ K, σ.app K = δl K M) :
    NatTrans.CommShift σ ℤ := by
  refine commShift_of_eq_transportBifunctorComparison GC GD pb τC τD δs (fun L => ?_)
    (fun L => ?_) hδs δl hδl h M σ hσ
  · exact NatTrans.commShift_of_eq_data
      (CommShift₂.precomp₁₂_commShiftFlipObj GC Tl CommShift₂Setup.int L)
      (CommShift₂.postcompInt_commShiftFlipObj Ts GC L) _ (hτC L)
  · have : NatTrans.CommShift ((CommShift₂.flipIso τD).app L).hom ℤ := hτD L
    have hinv := NatTrans.CommShift.of_iso_inv ((CommShift₂.flipIso τD).app L) ℤ
    exact NatTrans.commShift_of_eq_data
      (CommShift₂.postcompInt_commShiftFlipObj Ts' GD L)
      (CommShift₂.precomp₁₂_commShiftFlipObj GD Tl' CommShift₂Setup.int L) _ hinv

end Int

end CategoryTheory.Functor

end
