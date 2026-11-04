module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.PreEquivalenceRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.FppfCoverings

/-!
# Restricting a pre-relation and the quotient sheaf of the restriction

A pre-relation `j : R ⟶ U ×_Z U` restricts along a morphism `g : U' ⟶ U` over `Z`: the
restriction is the pullback of `j` along the self-product of `g`, and its two maps to `U'` are
the two projections of that pullback. Restriction preserves relations, pre-equivalence relations
and equivalence relations.

The second projection of the defining pullback is a morphism of pre-relations from the
restriction to `j` over `g`, so it induces a map `U'/R' ⟶ U/R` of quotient sheaves. That map is
always injective, and it is an isomorphism as soon as `g` is surjective as a map of fppf
sheaves — in particular when `{g}` is an fppf covering.

## Main definitions

* `AlgebraicGeometry.Space.PreRelation.restriction` and
  `AlgebraicGeometry.Space.PreRelation.restrict`: **Stacks 043D**, the restriction of a
  pre-relation along a morphism over `Z`.
* `AlgebraicGeometry.Space.restrictQuotientSheafMap`: the induced map `U'/R' ⟶ U/R`.

## Main results

* `AlgebraicGeometry.Space.PreRelation.isPreEquivalenceRelation_restrict` and
  `AlgebraicGeometry.Space.PreRelation.isEquivalenceRelation_restrict`: **Stacks 043D**,
  restriction preserves pre-equivalence relations and equivalence relations.
* `AlgebraicGeometry.Space.restrictQuotientSheafMap_mono`: **Stacks 046P**, injectivity.
* `AlgebraicGeometry.Space.restrictQuotientSheafMap_isIso`: **Stacks 046P**, bijectivity under
  local surjectivity of `g`.
* `AlgebraicGeometry.Space.restrictQuotientSheafMap_isIso_of_isFppfCovering`: **Stacks 046P**,
  the case of a one-element fppf covering.

## Implementation notes

Everything is stated for pre-relations on arbitrary objects of `CategoryTheory.Over Z`, that is
for arbitrary presheaves over `Z`, as in
`StacksFrontier/AlgebraicGeometry/Spaces/RelationsOverSpace.lean`; where the sheaf condition on `U`
or on `U'` is needed it is an explicit hypothesis rather than extracted from an algebraic space,
exactly as in `StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/Quotient/Sheaf.lean`. For an
algebraic space `U` the hypothesis is `U.left.property.isSheaf`, and in the fppf-covering case it
is supplied by the covering itself.

Injectivity is proved on sections: two sections of the restricted quotient sheaf agree locally
on a covering, because a section of `U` relating two sections of `U'` after a covering lifts to a
section of the restricted relation, and the quotient sheaf is separated. Surjectivity is formal:
the projection onto a quotient sheaf is an epimorphism of sheaves, and the comparison map is
therefore an epimorphism as soon as `g` is one.

A one-element fppf covering is turned into a local surjection by **Stacks 0469**, applied to the
coproduct over a singleton index type, whose canonical map to `U` is `g` itself.

## References

* [Stacks Project, Tag 043D](https://stacks.math.columbia.edu/tag/043D)
* [Stacks Project, Tag 046P](https://stacks.math.columbia.edu/tag/046P)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

universe u

variable {site : BigFppfSite.{u}} {S : Scheme.{u}} {hS : site.Contains S}
  {Z : (BigFppfOver site S hS)ᵒᵖ ⥤ Type u}

/-! ### Restriction of a pre-relation -/

namespace PreRelation

variable {R U U' : Over Z} (j : PreRelation R U)

/-- The presheaf over `Z` underlying the restriction of a pre-relation along `g`: the pullback
of `j` along the self-product of `g`. -/
noncomputable abbrev restriction (g : U' ⟶ U) : Over Z :=
  pullback (prod.map g g) j

/-- **Stacks 043D.** The restriction of a pre-relation along a morphism `g : U' ⟶ U` over `Z`,
that is the first projection of the pullback defining `restriction`. -/
@[stacks 043D "the restricted pre-relation",
  stacks 043E "the restriction `R|_{U'}` of a pre-relation along `g : U' ⟶ U`"]
noncomputable abbrev restrict (g : U' ⟶ U) : PreRelation (restriction j g) U' :=
  pullback.fst (prod.map g g) j

add_to_stacks 043D "preservation of relations" CategoryTheory.Limits.pullback.fst_of_mono

/-- The first projection of the restricted relation, composed with `g`, factors through `j`. -/
private theorem restrict_target_comp (g : U' ⟶ U) :
    (restrict j g).target ≫ g = pullback.snd (prod.map g g) j ≫ j.target := by
  dsimp [restrict, PreRelation.target]
  simp only [Category.assoc, ← pullback.condition_assoc]
  simp

/-- The second projection of the restricted relation, composed with `g`, factors through `j`. -/
private theorem restrict_source_comp (g : U' ⟶ U) :
    (restrict j g).source ≫ g = pullback.snd (prod.map g g) j ≫ j.source := by
  dsimp [restrict, PreRelation.source]
  simp only [Category.assoc, ← pullback.condition_assoc]
  simp

/-- **Stacks 043D.** Restriction preserves pre-equivalence relations. -/
@[stacks 043D "preservation of pre-equivalence relations"]
theorem isPreEquivalenceRelation_restrict (g : U' ⟶ U) (hj : IsPreEquivalenceRelation j) :
    IsPreEquivalenceRelation (restrict j g) := by
  intro T b
  have hg : g.left ≫ U.hom = U'.hom := Over.w g
  let Tb : Over Z := Over.mk b
  let pointHom : ∀ {V : Over Z}, TestPoint T b V → (Tb ⟶ V) := fun x ↦ Over.homMk x.1 x.2
  have liftRel : ∀ {x y : TestPoint T b U'},
      j.Rel b (mapTestPoint g x) (mapTestPoint g y) → (restrict j g).Rel b x y := by
    rintro x y ⟨r, hr₁, hr₂⟩
    have hcomm : prod.lift (pointHom x) (pointHom y) ≫ prod.map g g = pointHom r ≫ j :=
      prod.hom_ext
        (Over.OverMorphism.ext (by
          simpa [pointHom, PreRelation.target, mapTestPoint, Category.assoc] using hr₁.symm))
        (Over.OverMorphism.ext (by
          simpa [pointHom, PreRelation.source, mapTestPoint, Category.assoc] using hr₂.symm))
    let z : Tb ⟶ restriction j g :=
      pullback.lift (prod.lift (pointHom x) (pointHom y)) (pointHom r) hcomm
    refine ⟨⟨z.left, Over.w z⟩, ?_, ?_⟩
    · have hz : z ≫ (restrict j g).target = pointHom x := by
        dsimp only [restrict, PreRelation.target]
        rw [← Category.assoc, pullback.lift_fst, prod.lift_fst]
      simpa [pointHom] using congrArg (fun k : Tb ⟶ U' ↦ k.left) hz
    · have hz : z ≫ (restrict j g).source = pointHom y := by
        dsimp only [restrict, PreRelation.source]
        rw [← Category.assoc, pullback.lift_fst, prod.lift_snd]
      simpa [pointHom] using congrArg (fun k : Tb ⟶ U' ↦ k.left) hz
  have forgetRel : ∀ {x y : TestPoint T b U'},
      (restrict j g).Rel b x y → j.Rel b (mapTestPoint g x) (mapTestPoint g y) := by
    rintro x y ⟨r, hr₁, hr₂⟩
    let z : Tb ⟶ R := pointHom r ≫ pullback.snd (prod.map g g) j
    refine ⟨⟨z.left, Over.w z⟩, ?_, ?_⟩
    · have hr₁' : pointHom r ≫ (restrict j g).target = pointHom x :=
        Over.OverMorphism.ext hr₁
      have hz : z ≫ j.target = pointHom x ≫ g := by
        rw [← hr₁', Category.assoc, Category.assoc, restrict_target_comp]
      simpa [pointHom, mapTestPoint] using congrArg (fun k : Tb ⟶ U ↦ k.left) hz
    · have hr₂' : pointHom r ≫ (restrict j g).source = pointHom y :=
        Over.OverMorphism.ext hr₂
      have hz : z ≫ j.source = pointHom y ≫ g := by
        rw [← hr₂', Category.assoc, Category.assoc, restrict_source_comp]
      simpa [pointHom, mapTestPoint] using congrArg (fun k : Tb ⟶ U ↦ k.left) hz
  exact ⟨fun x ↦ liftRel ((hj T b).refl (mapTestPoint g x)),
    fun {_ _} h ↦ liftRel ((hj T b).symm (forgetRel h)),
    fun {_ _ _} hxy hyz ↦ liftRel ((hj T b).trans (forgetRel hxy) (forgetRel hyz))⟩

/-- **Stacks 043D.** Restriction preserves equivalence relations. -/
@[stacks 043D "preservation of equivalence relations"]
instance isEquivalenceRelation_restrict (g : U' ⟶ U)
    [hj : IsEquivalenceRelation j.target j.source] :
    IsEquivalenceRelation (restrict j g).target (restrict j g).source := by
  rw [isEquivalenceRelation_iff_mono_and_isPreEquivalenceRelation] at hj ⊢
  have _ : Mono j := hj.1
  exact ⟨inferInstance, isPreEquivalenceRelation_restrict j g hj.2⟩

end PreRelation

/-! ### The quotient sheaf of a restricted pre-relation -/

variable {R U U' : Over Z}

/-- A section of the restricted relation assembled from two sections of `U'` and a section of `R`
relating their images in `U`. -/
private theorem exists_restriction_section (j : PreRelation R U) (g : U' ⟶ U)
    (T : BigFppfOver site S hS) (a b : U'.left.obj (op T)) (r : R.left.obj (op T))
    (hs : g.left.app (op T) a = j.source.left.app (op T) r)
    (ht : g.left.app (op T) b = j.target.left.app (op T) r) :
    ∃ r' : (PreRelation.restriction j g).left.obj (op T),
      (PreRelation.restrict j g).source.left.app (op T) r' = a ∧
        (PreRelation.restrict j g).target.left.app (op T) r' = b := by
  let rMap : yoneda.obj T ⟶ R.left := yonedaEquiv.symm r
  let aMap : yoneda.obj T ⟶ U'.left := yonedaEquiv.symm a
  let bMap : yoneda.obj T ⟶ U'.left := yonedaEquiv.symm b
  have hsMap : aMap ≫ g.left = rMap ≫ j.source.left := by
    apply yonedaEquiv.injective
    simpa [aMap, rMap, yonedaEquiv] using hs
  have htMap : bMap ≫ g.left = rMap ≫ j.target.left := by
    apply yonedaEquiv.injective
    simpa [bMap, rMap, yonedaEquiv] using ht
  let W : Over Z := Over.mk (rMap ≫ R.hom)
  let rOver : W ⟶ R := Over.homMk rMap (by simp [W])
  have lift_to : ∀ (c : yoneda.obj T ⟶ U'.left) (e : R ⟶ U), c ≫ g.left = rMap ≫ e.left →
      ∃ cOver : W ⟶ U', cOver.left = c ∧ cOver ≫ g = rOver ≫ e := by
    intro c e h
    refine ⟨Over.homMk c ?_, rfl, Over.OverMorphism.ext h⟩
    change c ≫ U'.hom = rMap ≫ R.hom
    rw [← Over.w g, ← Category.assoc, h, Category.assoc, Over.w e]
  obtain ⟨aOver, haOver, hsOver⟩ := lift_to aMap j.source hsMap
  obtain ⟨bOver, hbOver, htOver⟩ := lift_to bMap j.target htMap
  have hpair : prod.lift bOver aOver ≫ prod.map g g = rOver ≫ j := by
    apply prod.hom_ext
    · simpa [PreRelation.target] using htOver
    · simpa [PreRelation.source] using hsOver
  let rOver' := pullback.lift (prod.lift bOver aOver) rOver hpair
  have eval : ∀ (p : PreRelation.restriction j g ⟶ U') (cOver : W ⟶ U'),
      rOver' ≫ p = cOver →
        p.left.app (op T) (yonedaEquiv rOver'.left) = yonedaEquiv cOver.left := by
    intro p cOver h
    rw [← yonedaEquiv_comp]
    exact congrArg yonedaEquiv (by simpa using congrArg (fun f : W ⟶ U' ↦ f.left) h)
  refine ⟨yonedaEquiv rOver'.left, ?_, ?_⟩
  · refine (eval (pullback.fst (prod.map g g) j ≫ prod.snd) aOver ?_).trans ?_
    · rw [← Category.assoc, pullback.lift_fst, prod.lift_snd]
    · simp [haOver, aMap]
  · refine (eval (pullback.fst (prod.map g g) j ≫ prod.fst) bOver ?_).trans ?_
    · rw [← Category.assoc, pullback.lift_fst, prod.lift_fst]
    · simp [hbOver, bMap]

variable [HasSheafify (BigFppfOver.topology site S hS) (Type u)]

/-- The projection of `U` onto its quotient sheaf is surjective as a map of fppf sheaves: a map
out of the quotient sheaf is determined by its restriction to `U`. -/
private theorem isLocallySurjective_toQuotientSheaf
    (hU : Presheaf.IsSheaf (BigFppfOver.topology site S hS) U.left) (j : PreRelation R U) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology site S hS) (toQuotientSheaf j) := by
  let J := BigFppfOver.topology site S hS
  let Uₛ : Sheaf J (Type u) := ⟨U.left, hU⟩
  let p : Uₛ ⟶ quotientSheaf j := ⟨toQuotientSheaf j⟩
  have hepi : Epi p := by
    constructor
    intro A f g h
    have hfg : toQuotientSheaf j ≫ f.hom = toQuotientSheaf j ≫ g.hom := by
      simpa [p] using congrArg (fun d : Uₛ ⟶ A ↦ d.hom) h
    have hk : j.target.left ≫ (toQuotientSheaf j ≫ f.hom) =
        j.source.left ≫ (toQuotientSheaf j ≫ f.hom) := by
      simpa [Category.assoc] using
        congrArg (fun q ↦ q ≫ f.hom) (target_toQuotientSheaf_eq_source j)
    exact (quotientSheafDesc_unique j A _ hk f rfl).trans
      (quotientSheafDesc_unique j A _ hk g hfg.symm).symm
  exact (Sheaf.isLocallySurjective_iff_epi p).2 hepi

/-- Every section of a quotient sheaf comes, on a covering of its test object, from a section
of `U`. -/
private theorem exists_local_toQuotientSheaf_preimage
    (hU : Presheaf.IsSheaf (BigFppfOver.topology site S hS) U.left) (j : PreRelation R U)
    (T : BigFppfOver site S hS) (x : (quotientSheaf j).obj.obj (op T)) :
    ∃ 𝒰 : (BigFppfOver.topology site S hS).Cover T,
      ∀ I : 𝒰.Arrow, ∃ a : U.left.obj (op I.Y),
        (quotientSheaf j).obj.map I.f.op x = (toQuotientSheaf j).app (op I.Y) a := by
  let J := BigFppfOver.topology site S hS
  let _ : Presheaf.IsLocallySurjective J (toQuotientSheaf j) :=
    isLocallySurjective_toQuotientSheaf hU j
  exact ⟨⟨Presheaf.imageSieve (toQuotientSheaf j) x,
      Presheaf.imageSieve_mem J (toQuotientSheaf j) x⟩,
    fun I ↦ ⟨Presheaf.localPreimage (toQuotientSheaf j) x I.f I.hf,
      (Presheaf.app_localPreimage (toQuotientSheaf j) x I.f I.hf).symm⟩⟩

/-- The map from the quotient sheaf of a restricted pre-relation to the quotient sheaf of the
original one, descended from the composite of `g` with the quotient projection. -/
noncomputable def restrictQuotientSheafMap (j : PreRelation R U) (g : U' ⟶ U) :
    quotientSheaf (PreRelation.restrict j g) ⟶ quotientSheaf j :=
  quotientSheafDesc (PreRelation.restrict j g) (quotientSheaf j)
    (g.left ≫ toQuotientSheaf j) (by
      have ht : (PreRelation.restrict j g).target ≫ g =
          pullback.snd (prod.map g g) j ≫ j.target := by
        dsimp [PreRelation.restrict, PreRelation.target]
        simp only [Category.assoc, ← pullback.condition_assoc]
        simp
      have hs : (PreRelation.restrict j g).source ≫ g =
          pullback.snd (prod.map g g) j ≫ j.source := by
        dsimp [PreRelation.restrict, PreRelation.source]
        simp only [Category.assoc, ← pullback.condition_assoc]
        simp
      have ht' := congrArg (fun f : PreRelation.restriction j g ⟶ U ↦ f.left) ht
      have hs' := congrArg (fun f : PreRelation.restriction j g ⟶ U ↦ f.left) hs
      simp only [PreRelation.target, PreRelation.source, Over.comp_left, Category.assoc]
        at ht' hs' ⊢
      simp only [← Category.assoc] at ht' hs' ⊢
      rw [ht', hs']
      simpa only [PreRelation.target, PreRelation.source, Over.comp_left, Category.assoc]
        using congrArg ((pullback.snd (prod.map g g) j).left ≫ ·)
          (target_toQuotientSheaf_eq_source j))

/-- The comparison map of quotient sheaves restricts to `g` on `U'`. -/
private theorem toQuotientSheaf_restrictQuotientSheafMap (j : PreRelation R U) (g : U' ⟶ U) :
    toQuotientSheaf (PreRelation.restrict j g) ≫ (restrictQuotientSheafMap j g).hom =
      g.left ≫ toQuotientSheaf j :=
  toQuotientSheaf_quotientSheafDesc _ _ _ _

/-- **Stacks 046P.** Restricting a pre-equivalence relation gives an injective map of quotient
sheaves. -/
@[stacks 046P "injectivity"]
theorem restrictQuotientSheafMap_mono (j : PreRelation R U) (g : U' ⟶ U)
    (hj : IsPreEquivalenceRelation j)
    (hU' : Presheaf.IsSheaf (BigFppfOver.topology site S hS) U'.left) :
    Mono (restrictQuotientSheafMap j g) := by
  let J := BigFppfOver.topology site S hS
  let j' := PreRelation.restrict j g
  let q := restrictQuotientSheafMap j g
  have hj' : IsPreEquivalenceRelation j' :=
    PreRelation.isPreEquivalenceRelation_restrict j g hj
  have hfac := toQuotientSheaf_restrictQuotientSheafMap j g
  have hmono : Mono q.hom := by
    rw [NatTrans.mono_iff_mono_app]
    intro T
    rw [CategoryTheory.mono_iff_injective]
    intro x y hxy
    obtain ⟨𝒰, hxrep⟩ := exists_local_toQuotientSheaf_preimage hU' j' T.unop x
    obtain ⟨𝒱, hyrep⟩ := exists_local_toQuotientSheaf_preimage hU' j' T.unop y
    let 𝒲 : J.Cover T.unop := ⟨𝒰.1 ⊓ 𝒱.1, J.intersection_covering 𝒰.2 𝒱.2⟩
    have hlocalArrows : ∀ I : 𝒲.Arrow,
        (quotientSheaf j').obj.map I.f.op x = (quotientSheaf j').obj.map I.f.op y := by
      intro I
      obtain ⟨a, hxa⟩ := hxrep ⟨I.Y, I.f, I.hf.1⟩
      obtain ⟨b, hyb⟩ := hyrep ⟨I.Y, I.f, I.hf.2⟩
      have hfactor (c : U'.left.obj (op I.Y)) :
          q.hom.app (op I.Y) ((toQuotientSheaf j').app (op I.Y) c) =
            (toQuotientSheaf j).app (op I.Y) (g.left.app (op I.Y) c) := by
        simpa only [NatTrans.comp_app, CategoryTheory.comp_apply] using
          congrArg (fun f ↦ f.app (op I.Y) c) hfac
      have hq : (toQuotientSheaf j).app (op I.Y) (g.left.app (op I.Y) a) =
          (toQuotientSheaf j).app (op I.Y) (g.left.app (op I.Y) b) := by
        rw [← hfactor a, ← hfactor b, ← hxa, ← hyb,
          NatTrans.naturality_apply q.hom I.f.op x, NatTrans.naturality_apply q.hom I.f.op y]
        exact congrArg ((quotientSheaf j).obj.map I.f.op) hxy
      obtain ⟨E, hE, hrel⟩ := (toQuotientSheaf_eq_iff_locally_related j hj I.Y
        (g.left.app (op I.Y) a) (g.left.app (op I.Y) b)).1 hq
      have hrel' : ∀ i : E.I₀, ∃ r' : (PreRelation.restriction j g).left.obj (op (E.X i)),
          (U'.left.map (E.f i).op a = j'.source.left.app (op (E.X i)) r') ∧
            (U'.left.map (E.f i).op b = j'.target.left.app (op (E.X i)) r') := by
        intro i
        obtain ⟨r, hsrc, htgt⟩ := hrel i
        have hsrc' : g.left.app (op (E.X i)) (U'.left.map (E.f i).op a) =
            j.source.left.app (op (E.X i)) r := by
          rwa [NatTrans.naturality_apply]
        have htgt' : g.left.app (op (E.X i)) (U'.left.map (E.f i).op b) =
            j.target.left.app (op (E.X i)) r := by
          rwa [NatTrans.naturality_apply]
        obtain ⟨r', hs, ht⟩ := exists_restriction_section j g (E.X i)
          (U'.left.map (E.f i).op a) (U'.left.map (E.f i).op b) r hsrc' htgt'
        exact ⟨r', hs.symm, ht.symm⟩
      calc _ = (toQuotientSheaf j').app (op I.Y) a := hxa
        _ = (toQuotientSheaf j').app (op I.Y) b :=
            (toQuotientSheaf_eq_iff_locally_related j' hj' I.Y a b).2 ⟨E, hE, hrel'⟩
        _ = _ := hyb.symm
    exact (quotientSheaf j').property.isSeparated T.unop 𝒲.1 𝒲.2 x y
      fun Y f hf ↦ hlocalArrows ⟨Y, f, hf⟩
  exact Sheaf.Hom.mono_of_presheaf_mono J (Type u) q

/-- **Stacks 046P.** If `g` is surjective as a map of fppf sheaves, then the induced map of
quotient sheaves is an isomorphism. -/
@[stacks 046P "isomorphism under surjectivity"]
theorem restrictQuotientSheafMap_isIso (j : PreRelation R U) (g : U' ⟶ U)
    (hj : IsPreEquivalenceRelation j)
    (hg : Presheaf.IsLocallySurjective (BigFppfOver.topology site S hS) g.left)
    (hU : Presheaf.IsSheaf (BigFppfOver.topology site S hS) U.left)
    (hU' : Presheaf.IsSheaf (BigFppfOver.topology site S hS) U'.left) :
    IsIso (restrictQuotientSheafMap j g) := by
  let J := BigFppfOver.topology site S hS
  let j' := PreRelation.restrict j g
  let Uₛ : Sheaf J (Type u) := ⟨U.left, hU⟩
  let U'ₛ : Sheaf J (Type u) := ⟨U'.left, hU'⟩
  let p : Uₛ ⟶ quotientSheaf j := ⟨toQuotientSheaf j⟩
  let p' : U'ₛ ⟶ quotientSheaf j' := ⟨toQuotientSheaf j'⟩
  let gs : U'ₛ ⟶ Uₛ := ⟨g.left⟩
  let q := restrictQuotientSheafMap j g
  have _ : Epi p :=
    (Sheaf.isLocallySurjective_iff_epi p).1 (isLocallySurjective_toQuotientSheaf hU j)
  have _ : Epi gs := (Sheaf.isLocallySurjective_iff_epi gs).1 hg
  have hfactor : p' ≫ q = gs ≫ p :=
    Sheaf.hom_ext (toQuotientSheaf_restrictQuotientSheafMap j g)
  have _ : Epi (p' ≫ q) := by rw [hfactor]; infer_instance
  have _ : Epi q := epi_of_epi p' q
  have _ : Mono q := restrictQuotientSheafMap_mono j g hj hU'
  exact isIso_of_mono_of_epi q

/-- **Stacks 046P.** If `{g}` is a one-element fppf covering, then the induced map of quotient
sheaves is an isomorphism. -/
@[stacks 046P "fppf-covering case"]
theorem restrictQuotientSheafMap_isIso_of_isFppfCovering (j : PreRelation R U) (g : U' ⟶ U)
    (hj : IsPreEquivalenceRelation j)
    (hg : IsFppfCovering site S hS (fun _ : PUnit ↦ U'.left) (fun _ ↦ g.left)) :
    IsIso (restrictQuotientSheafMap j g) := by
  let J := BigFppfOver.topology site S hS
  let A : Sheaf J (Type u) := ⟨U'.left, (hg.source_isAlgebraicSpace PUnit.unit).isSheaf⟩
  let F : Sheaf J (Type u) := ⟨U.left, hg.target_isAlgebraicSpace.isSheaf⟩
  have hloc : Presheaf.IsLocallySurjective J g.left := by
    let hc := Cofan.isColimitMkOfUnique (Iso.refl A) PUnit
    have hs := isLocallySurjective_coproductDesc_of_isFppfCovering site S hS
      (fun _ : PUnit ↦ U'.left) (fun _ ↦ g.left) hg A (fun _ ↦ 𝟙 A) hc
    have he : hc.desc (Cofan.mk F (fun _ : PUnit ↦ (⟨g.left⟩ : A ⟶ F))) = (⟨g.left⟩ : A ⟶ F) := by
      simpa using hc.fac (Cofan.mk F (fun _ : PUnit ↦ (⟨g.left⟩ : A ⟶ F))) ⟨PUnit.unit⟩
    change Sheaf.IsLocallySurjective
      (hc.desc (Cofan.mk F (fun _ : PUnit ↦ (⟨g.left⟩ : A ⟶ F)))) at hs
    rwa [he] at hs
  exact restrictQuotientSheafMap_isIso j g hj hloc hg.target_isAlgebraicSpace.isSheaf
    (hg.source_isAlgebraicSpace PUnit.unit).isSheaf

end AlgebraicGeometry.Space

end
