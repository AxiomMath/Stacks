module

public import StacksFrontier.AlgebraicGeometry.Etale.DescentEffectivity.BaseChangeDescended
public import StacksFrontier.AlgebraicGeometry.Etale.DescentEffectivity.ChangeTransitivity
public import StacksFrontier.AlgebraicGeometry.Etale.DescentEffectivity.LimitPasting

/-!
# The gluing isomorphism of a scheme descending a base-changed descent datum

Let `f : X ⟶ S` be a surjective integral morphism, `D` a descent datum relative to `X / S` with
étale underlying scheme, and `w : W ⟶ S` a morphism of the base. A scheme `U` over `W`
descending the base change `D.changeDatum w` has two pullbacks to `W ×_S W`, one along each
projection, and both of them descend *one* descent datum: the base change of `D` along the
common composite `W ×_S W ⟶ W ⟶ S`. Since the étale descent functor of a surjective integral
morphism is fully faithful, and the projection of `W ×_S W` to `S` is one such composite, the
two pullbacks are therefore canonically isomorphic over `W ×_S W`
(`AlgebraicGeometry.DescentDatum.Descended.baseGluingIso`).

## Main definitions

* `AlgebraicGeometry.DescentDatum.Descended.ofIsoSquare`: **a scheme descending the pullback of a
  datum along an isomorphism square over the identity base descends the datum itself**, with the
  same descended scheme.
* `AlgebraicGeometry.DescentDatum.Descended.changeComp`: **transitivity of base change for a
  descended scheme**, the analogue of
  `AlgebraicGeometry.DescentDatum.isEtaleEffective_changeDatum_comp_iff` that keeps track of the
  descended scheme.
* `AlgebraicGeometry.DescentDatum.Descended.changeCongr`: transport of a descended scheme along
  an equality of base morphisms.
* `AlgebraicGeometry.DescentDatum.Descended.baseGluingIso` and
  `AlgebraicGeometry.DescentDatum.Descended.baseGluingPullbackIso`: **the gluing isomorphism of
  the two pullbacks of a descended scheme to `W ×_S W`**, in the base-change formalism and on the
  literal fibre products.

## Main results

* `AlgebraicGeometry.exists_descended_etale_of_isEtaleEffective`: an étale effective datum
  carries a descended scheme which is étale over the base, the converse of
  `AlgebraicGeometry.DescentDatum.Descended.isEtaleEffective`.
* `AlgebraicGeometry.DescentDatum.Descended.baseGluingPullbackIso_hom_fst` and
  `AlgebraicGeometry.DescentDatum.Descended.baseGluingPullbackIso_hom_snd`: the gluing
  isomorphism lies over `W ×_S W`.

## References

* [Stacks Project, Tag 02W8](https://stacks.math.columbia.edu/tag/02W8)
* [Stacks Project, Tag 0BTP](https://stacks.math.columbia.edu/tag/0BTP)
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory Limits

/-- The base change along an arbitrary morphism of an étale scheme over the base is étale. -/
instance etale_overPullback_obj_hom {W T : Scheme.{u}} (p : T ⟶ W) (B : Over W)
    [Etale B.hom] : Etale ((Over.pullback p).obj B).hom := by
  change Etale (pullback.snd B.hom p)
  infer_instance

/-- **An étale effective descent datum carries a descended scheme which is étale over the
base.** This is the converse of
`AlgebraicGeometry.DescentDatum.Descended.isEtaleEffective`. -/
theorem exists_descended_etale_of_isEtaleEffective {S X : Scheme.{u}} {f : X ⟶ S}
    (D : DescentDatum f) [Etale D.over.hom] (h : D.IsEtaleEffective) :
    ∃ Q : D.Descended, Etale Q.base.hom :=
  ⟨DescentDatum.Descended.ofIso ((IsEtaleDescentData f).ι.mapIso h.getIso), h.witness.prop⟩

namespace DescentDatum.Descended

/-! ### Reflection along an isomorphism square -/

section IsoSquare

variable {S X X' : Scheme.{u}} {a : X ⟶ S} {a' : X' ⟶ S} {e : X' ⟶ X}
  {comm : e ≫ a = a' ≫ 𝟙 S} (P : DescentData.PullbackFunctor a a' (𝟙 S) e comm)
  (D : DescentDatum a)

/-- The comparison of the underlying scheme of the pullback of a datum along a square with the
underlying scheme of the datum itself: the identification with the base change along the
square's top map, followed by the projection of that base change. -/
def squareOver : (pullbackSquareDatum P D).over.left ⟶ D.over.left :=
  (P.objIso D).hom.left ≫ pullback.fst D.over.hom e

/-- For a square whose top map is an isomorphism the comparison of the underlying schemes is an
isomorphism. -/
instance isIso_squareOver [IsIso e] : IsIso (squareOver P D) := by
  have : IsIso ((P.objIso D).hom.left) :=
    inferInstanceAs (IsIso ((Over.forget X').map (P.objIso D).hom))
  rw [squareOver]
  infer_instance

/-- The comparison of the underlying schemes lies over the square's top map. -/
@[reassoc]
lemma squareOver_comp_over_hom :
    squareOver P D ≫ D.over.hom = (pullbackSquareDatum P D).over.hom ≫ e := by
  rw [squareOver, Category.assoc, pullback.condition, ← Category.assoc,
    objIso_hom_left_comp_snd]

include comm in
/-- Over the identity base the square's two structure morphisms agree after the top map. -/
lemma isoSquare_comp_eq : e ≫ a = a' := by simpa using comm

variable [IsIso e]

omit [IsIso e] in
/-- The first component of the induced map of sources is the comparison of the underlying
schemes. -/
@[reassoc]
lemma sourceMap_comp_fst :
    P.sourceMap D ≫ pullback.fst (D.over.hom ≫ a) a =
      pullback.fst ((pullbackSquareDatum P D).over.hom ≫ a') a' ≫ squareOver P D :=
  P.sourceMap_fst D

omit [IsIso e] in
/-- The second component of the induced map of targets is the comparison of the underlying
schemes. -/
@[reassoc]
lemma targetMap_comp_snd :
    P.targetMap D ≫ pullback.snd a (D.over.hom ≫ a) =
      pullback.snd a' ((pullbackSquareDatum P D).over.hom ≫ a') ≫ squareOver P D :=
  P.targetMap_snd D

include comm in
/-- The inverse of the comparison of the underlying schemes lies over the inverse of the
square's top map. -/
lemma inv_squareOver_comp_over_hom :
    inv (squareOver P D) ≫ (pullbackSquareDatum P D).over.hom = D.over.hom ≫ inv e := by
  rw [IsIso.inv_comp_eq, ← Category.assoc, squareOver_comp_over_hom, Category.assoc,
    IsIso.hom_inv_id, Category.comp_id]

include comm in
/-- The two inverse components of the induced map of sources agree over the base, so that they
define a morphism into the fibre product. -/
lemma sourceMap_cond :
    (pullback.fst (D.over.hom ≫ a) a ≫ inv (squareOver P D)) ≫
        ((pullbackSquareDatum P D).over.hom ≫ a') =
      (pullback.snd (D.over.hom ≫ a) a ≫ inv e) ≫ a' := by
  rw [Category.assoc, Category.assoc,
    reassoc_of% (inv_squareOver_comp_over_hom P D (comm := comm)),
    (IsIso.inv_comp_eq e).2 (isoSquare_comp_eq (comm := comm)).symm]
  exact pullback.condition

include comm in
/-- **The induced map of the sources of the two gluing isomorphisms is invertible** when the
square's top map is. Its two components are the comparison of the underlying schemes and the
square's top map, both isomorphisms. -/
instance isIso_sourceMap : IsIso (P.sourceMap D) := by
  refine ⟨pullback.lift (f := (pullbackSquareDatum P D).over.hom ≫ a') (g := a')
      (pullback.fst (D.over.hom ≫ a) a ≫ inv (squareOver P D))
      (pullback.snd (D.over.hom ≫ a) a ≫ inv e) (sourceMap_cond P D (comm := comm)), ?_, ?_⟩
  · refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, sourceMap_comp_fst_assoc,
        IsIso.hom_inv_id, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, reassoc_of% (P.sourceMap_snd D),
        IsIso.hom_inv_id, Category.comp_id, Category.id_comp]
  · refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, sourceMap_comp_fst, ← Category.assoc, pullback.lift_fst,
        Category.assoc, IsIso.inv_hom_id, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, P.sourceMap_snd D, ← Category.assoc, pullback.lift_snd,
        Category.assoc, IsIso.inv_hom_id, Category.comp_id, Category.id_comp]

include comm in
/-- **A scheme descending the pullback of a datum along an isomorphism square over the identity
base descends the datum itself.** The descended scheme is unchanged and the projection is
precomposed with the inverse of the comparison of the two underlying schemes. -/
def ofIsoSquare (Q : (pullbackSquareDatum P D).Descended) : D.Descended where
  base := Q.base
  proj := inv (squareOver P D) ≫ Q.proj
  isPullback := by
    refine Q.isPullback.of_iso' (asIso (squareOver P D)).symm (asIso e).symm
      (Iso.refl _) (Iso.refl _) ?_ (by simp) ?_ (by simp)
    · simpa using inv_squareOver_comp_over_hom P D (comm := comm)
    · simpa using (IsIso.inv_comp_eq e).2 (isoSquare_comp_eq (comm := comm)).symm
  proj_invariant := by
    rw [← cancel_epi (P.sourceMap D), ← reassoc_of% (P.gluing D),
      targetMap_comp_snd_assoc, IsIso.hom_inv_id_assoc,
      sourceMap_comp_fst_assoc, IsIso.hom_inv_id_assoc]
    exact Q.proj_invariant

include comm in
/-- The scheme of `ofIsoSquare` is the descended scheme it was built from. -/
@[simp]
lemma ofIsoSquare_base (Q : (pullbackSquareDatum P D).Descended) :
    (ofIsoSquare P D (comm := comm) Q).base = Q.base := rfl

include comm in
/-- The projection of `ofIsoSquare` is the original projection precomposed with the inverse of
the comparison of the underlying schemes. -/
@[simp]
lemma ofIsoSquare_proj (Q : (pullbackSquareDatum P D).Descended) :
    (ofIsoSquare P D (comm := comm) Q).proj = inv (squareOver P D) ≫ Q.proj := rfl

end IsoSquare

/-! ### Naturality of the base-changed projection -/

section PullbackSquareNaturality

variable {S S' X X' : Scheme.{u}} {a : X ⟶ S} {a' : X' ⟶ S'} {h : S' ⟶ S} {p : X' ⟶ X}
  {comm : p ≫ a = a' ≫ h} (P : DescentData.PullbackFunctor a a' h p comm) {D : DescentDatum a}

include comm in
/-- **The projection of the base change of a descended scheme is natural in the descended
scheme.** A morphism over the base compatible with the two projections stays compatible with the
two base-changed projections. -/
lemma pullbackSquareProj_comp_map (Q Q' : D.Descended) (φ : Q.base ⟶ Q'.base)
    (hφ : Q.proj ≫ φ.left = Q'.proj) :
    pullbackSquareProj P Q ≫ ((Over.pullback h).map φ).left = pullbackSquareProj P Q' := by
  refine pullback.hom_ext ?_ ?_
  · have h₁ : ((Over.pullback h).map φ).left ≫ pullback.fst Q'.base.hom h =
        pullback.fst Q.base.hom h ≫ φ.left := by
      simp only [Over.pullback_map_left]
      exact pullback.lift_fst _ _ _
    rw [Category.assoc, h₁, pullbackSquareProj_comp_fst_assoc, hφ,
      pullbackSquareProj_comp_fst]
  · have h₂ : ((Over.pullback h).map φ).left ≫ pullback.snd Q'.base.hom h =
        pullback.snd Q.base.hom h := by
      simp only [Over.pullback_map_left]
      exact pullback.lift_snd _ _ _
    rw [Category.assoc, h₂, pullbackSquareProj_comp_snd, pullbackSquareProj_comp_snd]

end PullbackSquareNaturality

/-! ### Transitivity of base change -/

section ChangeComp

variable {S X T T' : Scheme.{u}} {f : X ⟶ S} {D : DescentDatum f} {g : T ⟶ S}

/-- **Transitivity of base change for a scheme descending a descent datum.** The base change
along `g' : T' ⟶ T` of a scheme descending the base change of `D` along `g : T ⟶ S` descends the
base change of `D` along the composite. This is
`AlgebraicGeometry.DescentDatum.isEtaleEffective_changeDatum_comp_iff` with the descended scheme
kept track of. -/
def changeComp (Q : (D.changeDatum g).Descended) (g' : T' ⟶ T) :
    (D.changeDatum (g' ≫ g)).Descended :=
  ofIsoSquare (changeCompFunctor f g g') (D.changeDatum (g' ≫ g))
    (comm := changeCompIso_hom_comp_snd f g g')
    ((Q.changeDatum g').ofDatumIso (changeCompDatumIso g g' D))

/-- The scheme of `changeComp` is the base change of the descended scheme along `g'`. -/
@[simp]
lemma changeComp_base (Q : (D.changeDatum g).Descended) (g' : T' ⟶ T) :
    (Q.changeComp g').base = (Over.pullback g').obj Q.base := rfl

/-- **Transport of a scheme descending a base-changed datum along an equality of base
morphisms.** The descended scheme is unchanged. -/
def changeCongr {g₁ g₂ : T ⟶ S} (h : g₁ = g₂) (Q : (D.changeDatum g₁).Descended) :
    (D.changeDatum g₂).Descended where
  base := Q.base
  proj := h ▸ Q.proj
  isPullback := by subst h; exact Q.isPullback
  proj_invariant := by subst h; exact Q.proj_invariant

/-- The scheme of `changeCongr` is the descended scheme it was built from. -/
@[simp]
lemma changeCongr_base {g₁ g₂ : T ⟶ S} (h : g₁ = g₂) (Q : (D.changeDatum g₁).Descended) :
    (changeCongr h Q).base = Q.base := rfl

/-- The scheme of `changeComp` of an étale descended scheme is étale. -/
instance etale_changeComp_base_hom (Q : (D.changeDatum g).Descended) [Etale Q.base.hom]
    (g' : T' ⟶ T) : Etale (Q.changeComp g').base.hom := by
  change Etale ((Over.pullback g').obj Q.base).hom
  infer_instance

/-- The scheme of `changeCongr` of an étale descended scheme is étale. -/
instance etale_changeCongr_base_hom {g₁ g₂ : T ⟶ S} (h : g₁ = g₂)
    (Q : (D.changeDatum g₁).Descended) [Etale Q.base.hom] :
    Etale (changeCongr h Q).base.hom :=
  inferInstanceAs (Etale Q.base.hom)

/-- The projection of `changeComp` is the base-changed projection, precomposed with the
identification of the two data and the inverse of the comparison of the underlying schemes. -/
lemma changeComp_proj (Q : (D.changeDatum g).Descended) (g' : T' ⟶ T) :
    (Q.changeComp g').proj =
      inv (squareOver (changeCompFunctor f g g') (D.changeDatum (g' ≫ g))) ≫
        ((changeCompDatumIso g g' D).hom.hom ()).left ≫
          pullbackSquareProj (changePullbackFunctor (pullback.snd f g) g') Q := rfl

/-- **The projection of the iterated base change of a descended scheme is natural in the
descended scheme.** -/
lemma changeComp_proj_comp_map (Q Q' : (D.changeDatum g).Descended) (φ : Q.base ⟶ Q'.base)
    (hφ : Q.proj ≫ φ.left = Q'.proj) (g' : T' ⟶ T) :
    (Q.changeComp g').proj ≫ ((Over.pullback g').map φ).left = (Q'.changeComp g').proj := by
  show (inv (squareOver (changeCompFunctor f g g') (D.changeDatum (g' ≫ g))) ≫
      ((changeCompDatumIso g g' D).hom.hom ()).left ≫
        pullbackSquareProj (changePullbackFunctor (pullback.snd f g) g') Q) ≫
      ((Over.pullback g').map φ).left = _
  rw [Category.assoc, Category.assoc,
    pullbackSquareProj_comp_map (changePullbackFunctor (pullback.snd f g) g') Q Q' φ hφ]
  rfl

/-- **The comparison of two schemes descending one base-changed datum is compatible with
further base change.** The base change of the comparison satisfies the property characterising
the comparison of the two base-changed descended schemes, hence is it. -/
lemma map_compareOfFullyFaithful
    (hff : (etaleDescentFunctor (pullback.snd f g)).FullyFaithful) (g' : T' ⟶ T)
    (hff' : (etaleDescentFunctor (pullback.snd f (g' ≫ g))).FullyFaithful)
    (Q Q' : (D.changeDatum g).Descended) [Etale Q.base.hom] [Etale Q'.base.hom] :
    (Over.pullback g').map (compareOfFullyFaithful hff Q Q') =
      compareOfFullyFaithful hff' (Q.changeComp g') (Q'.changeComp g') :=
  eq_compareOfFullyFaithful hff' (Q.changeComp g') (Q'.changeComp g')
    (changeComp_proj_comp_map Q Q' _ (proj_comp_compareOfFullyFaithful hff Q Q') g')

end ChangeComp

/-! ### The gluing isomorphism over the self-fibre product of the base -/

section BaseGluing

variable {S X W : Scheme.{u}} {f : X ⟶ S} [Surjective f] [IsIntegralHom f]
  {D : DescentDatum f} {w : W ⟶ S} (Q : (D.changeDatum w).Descended) [Etale Q.base.hom]

/-- The pullback along the first projection of `W ×_S W` of a scheme descending the base change
of `D` along `w`, read as a scheme descending the base change of `D` along
`pullback.fst w w ≫ w`. -/
abbrev fstPullbackDescended : (D.changeDatum (pullback.fst w w ≫ w)).Descended :=
  Q.changeComp (pullback.fst w w)

/-- The pullback along the second projection of `W ×_S W` of a scheme descending the base change
of `D` along `w`, read as a scheme descending the base change of `D` along the *first*
projection's composite — the two composites `W ×_S W ⟶ S` being equal. -/
abbrev sndPullbackDescended : (D.changeDatum (pullback.fst w w ≫ w)).Descended :=
  changeCongr pullback.condition.symm (Q.changeComp (pullback.snd w w))

/-- The scheme of `fstPullbackDescended` is étale. -/
instance etale_fstPullbackDescended_base_hom :
    Etale (fstPullbackDescended Q).base.hom := by
  change Etale ((Over.pullback (pullback.fst w w)).obj Q.base).hom
  infer_instance

/-- The scheme of `sndPullbackDescended` is étale. -/
instance etale_sndPullbackDescended_base_hom :
    Etale (sndPullbackDescended Q).base.hom := by
  change Etale ((Over.pullback (pullback.snd w w)).obj Q.base).hom
  infer_instance

/-- **The étale descent functor over the self-fibre product of the base is fully faithful**, the
morphism there being a base change of the surjective integral `f`. -/
theorem nonempty_fullyFaithful_etaleDescentFunctor_baseSelfProduct (f : X ⟶ S) [Surjective f]
    [IsIntegralHom f] (w : W ⟶ S) :
    Nonempty (etaleDescentFunctor (pullback.snd f (pullback.fst w w ≫ w))).FullyFaithful :=
  etaleDescentFunctor_fullyFaithful_of_universallyClosed _

variable (hff : (etaleDescentFunctor (pullback.snd f (pullback.fst w w ≫ w))).FullyFaithful)

/-- **The gluing isomorphism of a scheme descending a base-changed descent datum.** The two
pullbacks to `W ×_S W` of a scheme descending `D.changeDatum w` descend one and the same datum,
so the full faithfulness of the étale descent functor over `W ×_S W` identifies them. -/
def baseGluingIso :
    (Over.pullback (pullback.fst w w)).obj Q.base ≅
      (Over.pullback (pullback.snd w w)).obj Q.base :=
  compareIsoOfFullyFaithful hff (fstPullbackDescended Q) (sndPullbackDescended Q)

/-- **The gluing isomorphism on the literal fibre products**: the isomorphism `U ×_S W ≅ W ×_S U`
over `W ×_S W` induced by `baseGluingIso`. -/
def baseGluingPullbackIso :
    pullback (Q.base.hom ≫ w) w ≅ pullback w (Q.base.hom ≫ w) :=
  DescentDatum.pullbackIsoOfBaseChangeIso w Q.base (baseGluingIso Q hff)

omit [Surjective f] [IsIntegralHom f] in
/-- The gluing isomorphism on the literal fibre products commutes with the maps to the first
factor of `W ×_S W`. -/
lemma baseGluingPullbackIso_hom_fst :
    (baseGluingPullbackIso Q hff).hom ≫ pullback.fst w (Q.base.hom ≫ w) =
      pullback.fst (Q.base.hom ≫ w) w ≫ Q.base.hom :=
  DescentDatum.pullbackIsoOfBaseChangeIso_hom_fst w Q.base (baseGluingIso Q hff)

omit [Surjective f] [IsIntegralHom f] in
/-- The gluing isomorphism on the literal fibre products commutes with the maps to the second
factor of `W ×_S W`. -/
lemma baseGluingPullbackIso_hom_snd :
    (baseGluingPullbackIso Q hff).hom ≫ pullback.snd w (Q.base.hom ≫ w) ≫ Q.base.hom =
      pullback.snd (Q.base.hom ≫ w) w :=
  DescentDatum.pullbackIsoOfBaseChangeIso_hom_snd w Q.base (baseGluingIso Q hff)

end BaseGluing

end DescentDatum.Descended

end AlgebraicGeometry

end
