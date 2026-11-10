module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.Sheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.InvariantMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.InvariantBaseChange

/-!
# Invariant morphisms and the quotient sheaf

A morphism out of `U` is invariant under a pre-relation `j : R ⟶ U ×_Z U` exactly when it
factors through the quotient sheaf `U/R` of **Stacks 044J**. This is the universal property of
the quotient sheaf read as a characterization of invariance.

Taking the quotient sheaf also commutes with base change along the invariant morphism: if `φ`
is invariant under `j` and `f : X' ⟶ X` is arbitrary, then the quotient sheaf of the
base-changed pre-relation of **Stacks 048G** is the fibre product of `X'` and `U/R` over `X`.

## Main results

* `AlgebraicGeometry.Space.invariant_iff_factors_through_quotientSheaf`: **Stacks 048F**, a
  morphism from `U` to a sheaf identifies the two endpoints of every arrow of `j` if and only
  if it factors through the canonical projection onto the quotient sheaf.
* `AlgebraicGeometry.Space.quotientSheaf_isPullback_baseChange`: **Stacks 0DTF**, the three
  canonical maps out of the two quotient sheaves, and the assertion that they form a cartesian
  square together with `f`.

## Implementation notes

The quotient need not be an algebraic space, so the factorization is through a morphism of
sheaves into the target read as a sheaf, `AlgebraicGeometry.Space.baseSheaf`; for an algebraic
space `X` the sheaf condition is `X.property.isSheaf`. The factorization is unique by
`AlgebraicGeometry.Space.quotientSheafDesc_unique`, so only its existence has to be asserted.

Invariance is `AlgebraicGeometry.Space.IsInvariant` of **Stacks 048E**, which is stated over
an arbitrary base object of an arbitrary category whose slice has binary products and so
applies to the slice of presheaves the quotient sheaf is built in.

The cartesian square is produced in two steps. The corresponding square of quotient
*presheaves* is cartesian with no sheaf hypothesis at all, and is checked degreewise: in each
degree `AlgebraicGeometry.Space.quotientPresheaf_obj_equiv` identifies the quotient presheaf
with a `Quot` of the one-step endpoint relation, and the statement becomes an assertion about
sets, which is the content of this file's private set-level lemmas. Sheafification then
preserves that square because it is left exact, and the counit of the sheafification
adjunction is an isomorphism at a sheaf, which removes the sheafifications of `X` and of `X'`
from the square. The three maps out of the quotient sheaves are specified by their composites
with the quotient projections rather than named, so that no choice of fibre product is made.

## References

* [Stacks Project, Tag 044J](https://stacks.math.columbia.edu/tag/044J)
* [Stacks Project, Tag 048E](https://stacks.math.columbia.edu/tag/048E)
* [Stacks Project, Tag 048F](https://stacks.math.columbia.edu/tag/048F)
* [Stacks Project, Tag 048G](https://stacks.math.columbia.edu/tag/048G)
* [Stacks Project, Tag 0DTF](https://stacks.math.columbia.edu/tag/0DTF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {site : BigFppfSite.{u}} {S : Scheme.{u}} {hS : site.Contains S}
  {Z : (BigFppfOver site S hS)ᵒᵖ ⥤ Type u} {R U : Over Z}
  {X : (BigFppfOver site S hS)ᵒᵖ ⥤ Type u}
  [HasSheafify (BigFppfOver.topology site S hS) (Type u)]

/-- **Stacks 048F.** A morphism from `U` to a sheaf is invariant under a pre-relation `j` if
and only if it factors through the canonical projection of `U` onto the quotient sheaf
`U/R`. -/
@[stacks 048F]
theorem invariant_iff_factors_through_quotientSheaf (j : PreRelation R U)
    (hX : Presheaf.IsSheaf (BigFppfOver.topology site S hS) X) (φ : U.left ⟶ X) :
    IsInvariant j φ ↔
      ∃ d : quotientSheaf j ⟶ baseSheaf hX, toQuotientSheaf j ≫ d.hom = φ := by
  refine ⟨fun h ↦ ⟨quotientSheafDesc j _ φ h, toQuotientSheaf_quotientSheafDesc _ _ _ _⟩, ?_⟩
  rintro ⟨d, hd⟩
  calc j.target.left ≫ φ
      = j.target.left ≫ toQuotientSheaf j ≫ d.hom := by rw [hd]
    _ = j.source.left ≫ toQuotientSheaf j ≫ d.hom := by
        rw [← Category.assoc, target_toQuotientSheaf_eq_source, Category.assoc]
    _ = j.source.left ≫ φ := by rw [hd]

/-! ### Base change of a quotient by an invariant relation, pointwise

The cartesian square of quotient sheaves is checked degreewise, where
`AlgebraicGeometry.Space.quotientPresheaf_obj_equiv` turns the quotient presheaf into a `Quot`
of the one-step endpoint relation. The four statements of this section are the resulting
assertion about sets alone.
-/

/-- A map which identifies the two endpoints of every arrow identifies any two points joined
by a chain of arrows. -/
private theorem eq_of_eqvGen_coequalizerRel {A P T : Type u} (s t : P → A) (ψ : A → T)
    (hinv : ∀ r, ψ (s r) = ψ (t r)) {a b : A}
    (h : Relation.EqvGen (Function.Coequalizer.Rel s t) a b) : ψ a = ψ b := by
  induction h with
  | rel a b h => cases h with | intro r => exact hinv r
  | refl a => rfl
  | symm a b h ih => exact ih.symm
  | trans a b c h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The quotient of `A` by the one-step endpoint relation of a pair of maps is the coequalizer
of that pair. -/
private def quotEndpointRelEquiv {A P : Type u} (s t : P → A) :
    Quot (fun x y : A => ∃ r, s r = x ∧ t r = y) ≃
      Quot (Function.Coequalizer.Rel s t) where
  toFun := Quot.lift (fun x => Quot.mk _ x) (by
    rintro x y ⟨r, rfl, rfl⟩
    exact Quot.sound (.intro r))
  invFun := Quot.lift (fun x => Quot.mk _ x) (by
    rintro x y ⟨r⟩
    exact Quot.sound ⟨r, rfl, rfl⟩)
  left_inv q := by induction q using Quot.inductionOn with | h x => rfl
  right_inv q := by induction q using Quot.inductionOn with | h x => rfl

/-- An isomorphism of pairs of maps induces an isomorphism from the quotient by the one-step
endpoint relation of the first pair to the coequalizer of the second. -/
private def quotEndpointRelEquivCoequalizer {A P A' P' : Type u}
    (s t : P → A) (s' t' : P' → A') (eA : A ≃ A') (eP : P ≃ P')
    (hs : ∀ r, eA (s r) = s' (eP r)) (ht : ∀ r, eA (t r) = t' (eP r)) :
    Quot (fun x y : A => ∃ r, s r = x ∧ t r = y) ≃
      Quot (Function.Coequalizer.Rel s' t') :=
  Quot.congr eA (by
    refine fun a b ↦ ⟨?_, fun h ↦ ?_⟩
    · rintro ⟨r, rfl, rfl⟩
      rw [hs, ht]
      exact .intro (eP r)
    · have hex : ∀ {x y}, Function.Coequalizer.Rel s' t' x y →
          ∃ r', s' r' = x ∧ t' r' = y := by
        intro x y hxy
        cases hxy with | intro r' => exact ⟨r', rfl, rfl⟩
      obtain ⟨r', h₁, h₂⟩ := hex h
      obtain ⟨r, rfl⟩ := eP.surjective r'
      exact ⟨r, eA.injective ((hs r).trans h₁), eA.injective ((ht r).trans h₂)⟩)

/-- A map to a type identified with a quotient, compatibly with the canonical classes, is
surjective. -/
private theorem surjective_of_equiv_quot {A Q : Type u} {r : A → A → Prop}
    (e : Q ≃ Quot r) (π : A → Q) (hπ : ∀ a, e (π a) = Quot.mk r a) :
    Function.Surjective π := fun q ↦ by
  obtain ⟨a, ha⟩ := Quot.exists_rep (e q)
  exact ⟨a, e.injective ((hπ a).trans ha)⟩

/-- The set-level statement behind **Stacks 0DTF**: for maps `s t : P → A`, an invariant
`ψ : A → T` and any `g : T' ⟶ T`, the coequalizer of the pair obtained by pulling `A` and `P`
back along `g` is the fibre product of `T'` and the coequalizer of `s` and `t` over `T`. -/
private theorem isPullback_coequalizer_baseChange_type
    {A P T T' : Type u} (s t : P → A) (ψ : A → T) (g : T' → T)
    (hinv : ∀ r, ψ (s r) = ψ (t r)) :
    let A' := {p : T' × A // g p.1 = ψ p.2}
    let P' := {p : T' × P // g p.1 = ψ (s p.2)}
    let s' : P' → A' := fun r => ⟨⟨r.1.1, s r.1.2⟩, r.2⟩
    let t' : P' → A' := fun r => ⟨⟨r.1.1, t r.1.2⟩, r.2.trans (hinv r.1.2)⟩
    let uMap : Quot (Function.Coequalizer.Rel s' t') → T' :=
      Quot.lift (fun a' => a'.1.1) (by intro a b h; cases h; rfl)
    let qMap : Quot (Function.Coequalizer.Rel s' t') →
        Quot (Function.Coequalizer.Rel s t) :=
      Quot.lift (fun a' => Quot.mk _ a'.1.2) (by
        rintro a b ⟨r⟩
        exact Quot.sound (.intro r.1.2))
    let ψMap : Quot (Function.Coequalizer.Rel s t) → T :=
      Quot.lift ψ (by rintro a b ⟨r⟩; exact hinv r)
    IsPullback (↾uMap) (↾qMap) (↾g) (↾ψMap) := by
  classical
  dsimp
  let A' := {p : T' × A // g p.1 = ψ p.2}
  let P' := {p : T' × P // g p.1 = ψ (s p.2)}
  let s' : P' → A' := fun r => ⟨⟨r.1.1, s r.1.2⟩, r.2⟩
  let t' : P' → A' := fun r => ⟨⟨r.1.1, t r.1.2⟩, r.2.trans (hinv r.1.2)⟩
  refine (Types.isPullback_iff _ _ _ _).2 ⟨?_, ?_, ?_⟩
  · ext z
    induction z using Quot.inductionOn with
    | h a =>
      change g a.1.1 = ψ a.1.2
      exact a.2
  · rintro z w ⟨hz, hw⟩
    induction z using Quot.inductionOn with
    | h a =>
      induction w using Quot.inductionOn with
      | h b =>
        obtain ⟨⟨ya, xa⟩, ha⟩ := a
        obtain ⟨⟨yb, xb⟩, hb⟩ := b
        obtain rfl : ya = yb := hz
        have hgen : Relation.EqvGen (Function.Coequalizer.Rel s t) xa xb :=
          Quot.eqvGen_exact (show Quot.mk (Function.Coequalizer.Rel s t) xa =
            Quot.mk (Function.Coequalizer.Rel s t) xb from hw)
        refine Quot.eqvGen_sound ?_
        have liftPath : ∀ {x y : A}
            (hxy : Relation.EqvGen (Function.Coequalizer.Rel s t) x y)
            (hx : g ya = ψ x) (hy : g ya = ψ y),
            Relation.EqvGen (Function.Coequalizer.Rel s' t')
              ⟨⟨ya, x⟩, hx⟩ ⟨⟨ya, y⟩, hy⟩ := by
          intro x y hxy
          induction hxy with
          | rel x y h =>
            obtain ⟨r⟩ := h
            intro hx hy
            exact .rel _ _ (Function.Coequalizer.Rel.intro (⟨⟨ya, r⟩, hx⟩ : P'))
          | refl x => exact fun _ _ ↦ .refl _
          | symm x y _ ih => exact fun hx hy ↦ .symm _ _ (ih hy hx)
          | trans x y z hxy _ ih₁ ih₂ =>
            intro hx hz
            exact Relation.EqvGen.trans _ _ _
              (ih₁ hx (hx.trans (eq_of_eqvGen_coequalizerRel s t ψ hinv hxy)))
              (ih₂ (hx.trans (eq_of_eqvGen_coequalizerRel s t ψ hinv hxy)) hz)
        exact liftPath hgen ha hb
  · intro y q h
    obtain ⟨a, rfl⟩ := Quot.exists_rep q
    exact ⟨Quot.mk _ ⟨⟨y, a⟩, by simpa using h⟩, rfl, rfl⟩

/-! ### Base change of a quotient by an invariant relation -/

/-- Sheafifying a morphism into a sheaf and composing with the counit of sheafification
recovers the morphism on the original presheaf. -/
private theorem toSheafify_presheafToSheaf_map_comp_counit
    {P : (BigFppfOver site S hS)ᵒᵖ ⥤ Type u}
    (A : Sheaf (BigFppfOver.topology site S hS) (Type u)) (d : P ⟶ A.obj) :
    toSheafify (BigFppfOver.topology site S hS) P ≫
        ((presheafToSheaf (BigFppfOver.topology site S hS) (Type u)).map d ≫
          (sheafificationAdjunction (BigFppfOver.topology site S hS) (Type u)).counit.app A).hom
      = d := by
  simp [ObjectProperty.FullSubcategory.comp_hom]

/-- Sheafifying the descent of an invariant morphism to the quotient presheaf and composing
with the counit of sheafification at a sheaf gives back the morphism on `U`. -/
private theorem toQuotientSheaf_presheafToSheaf_map_desc (j : PreRelation R U)
    (A : Sheaf (BigFppfOver.topology site S hS) (Type u)) (k : U.left ⟶ A.obj)
    (hk : j.target.left ≫ k = j.source.left ≫ k) :
    toQuotientSheaf j ≫
        ((presheafToSheaf (BigFppfOver.topology site S hS) (Type u)).map
            (coequalizer.desc (f := j.target.left) (g := j.source.left) k hk) ≫
          (sheafificationAdjunction (BigFppfOver.topology site S hS) (Type u)).counit.app A).hom
      = k :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun m ↦ coequalizer.π j.target.left j.source.left ≫ m)
        (toSheafify_presheafToSheaf_map_comp_counit A
          (coequalizer.desc (f := j.target.left) (g := j.source.left) k hk))).trans
      (coequalizer.π_desc k hk))

variable {X' : (BigFppfOver site S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 0DTF.** The quotient sheaf of the base change of an invariant pre-relation along
`f : X' ⟶ X` is the fibre product of `X'` and the original quotient sheaf over `X`. The three
canonical maps are specified by their composites with the quotient projections. -/
@[stacks 0DTF]
theorem quotientSheaf_isPullback_baseChange (j : PreRelation R U)
    (hX : Presheaf.IsSheaf (BigFppfOver.topology site S hS) X)
    (hX' : Presheaf.IsSheaf (BigFppfOver.topology site S hS) X')
    (φ : U.left ⟶ X) (f : X' ⟶ X) (hφ : IsInvariant j φ) :
    let j' := (baseChangedPreRelation j φ f hφ).val
    ∃ (qToX : quotientSheaf j ⟶ baseSheaf hX)
      (q'ToX' : quotientSheaf j' ⟶ baseSheaf hX')
      (q'ToQ : quotientSheaf j' ⟶ quotientSheaf j),
      (toQuotientSheaf j ≫ qToX.hom = φ) ∧
      (toQuotientSheaf j' ≫ q'ToX'.hom = pullback.fst f φ) ∧
      (toQuotientSheaf j' ≫ q'ToQ.hom = pullback.snd f φ ≫ toQuotientSheaf j) ∧
      IsPullback q'ToX' q'ToQ ⟨f⟩ qToX := by
  classical
  intro j'
  have hj' := (baseChangedPreRelation j φ f hφ).property
  have hInv' : IsInvariant j' (pullback.fst f φ) := hj'.1.1.trans hj'.2.1.symm
  -- the same square, for the quotient *presheaves*: it is cartesian degreewise
  let πj := coequalizer.π j.target.left j.source.left
  let πj' := coequalizer.π j'.target.left j'.source.left
  let dToX : quotientPresheaf j ⟶ X :=
    coequalizer.desc (f := j.target.left) (g := j.source.left) φ hφ
  let dToX' : quotientPresheaf j' ⟶ X' :=
    coequalizer.desc (f := j'.target.left) (g := j'.source.left) (pullback.fst f φ) hInv'
  have hkToQ : j'.target.left ≫ pullback.snd f φ ≫ πj =
      j'.source.left ≫ pullback.snd f φ ≫ πj := by
    calc j'.target.left ≫ pullback.snd f φ ≫ πj
        = (j'.target.left ≫ pullback.snd f φ) ≫ πj := (Category.assoc _ _ _).symm
      _ = pullback.snd f (j.target.left ≫ φ) ≫ j.target.left ≫ πj := by
          rw [hj'.1.2, Category.assoc]
      _ = pullback.snd f (j.target.left ≫ φ) ≫ j.source.left ≫ πj := by
          rw [coequalizer.condition]
      _ = (j'.source.left ≫ pullback.snd f φ) ≫ πj := by rw [hj'.2.2, Category.assoc]
      _ = j'.source.left ≫ pullback.snd f φ ≫ πj := Category.assoc _ _ _
  let dToQ : quotientPresheaf j' ⟶ quotientPresheaf j :=
    coequalizer.desc (f := j'.target.left) (g := j'.source.left) (pullback.snd f φ ≫ πj) hkToQ
  have hPresheaf : IsPullback dToX' dToQ f dToX := by
    refine IsPullback.of_forall_isPullback_app ?_
    intro T
    have hinvT : ∀ r, φ.app T (j.target.left.app T r) = φ.app T (j.source.left.app T r) :=
      fun r ↦ congrArg (fun m : R.left ⟶ X ↦ m.app T r) hφ
    let AGen : Type u := {p : X'.obj T × U.left.obj T // f.app T p.1 = φ.app T p.2}
    let PGen : Type u :=
      {p : X'.obj T × R.left.obj T // f.app T p.1 = φ.app T (j.target.left.app T p.2)}
    let sGen : PGen → AGen := fun r ↦ ⟨⟨r.1.1, j.target.left.app T r.1.2⟩, r.2⟩
    let tGen : PGen → AGen :=
      fun r ↦ ⟨⟨r.1.1, j.source.left.app T r.1.2⟩, r.2.trans (hinvT r.1.2)⟩
    have hApp : IsPullback ((pullback.fst f φ).app T) ((pullback.snd f φ).app T)
        (f.app T) (φ.app T) := (IsPullback.of_hasPullback f φ).app T
    have hAppR : IsPullback ((pullback.fst f (j.target.left ≫ φ)).app T)
        ((pullback.snd f (j.target.left ≫ φ)).app T) (f.app T)
        ((j.target.left ≫ φ).app T) := (IsPullback.of_hasPullback f _).app T
    let eA := PullbackCone.IsLimit.equivPullbackObj hApp.isLimit
    let eR := PullbackCone.IsLimit.equivPullbackObj hAppR.isLimit
    have eA_fst (a) : (eA a).1.1 = (pullback.fst f φ).app T a :=
      PullbackCone.IsLimit.equivPullbackObj_apply_fst hApp.isLimit a
    have eA_snd (a) : (eA a).1.2 = (pullback.snd f φ).app T a :=
      PullbackCone.IsLimit.equivPullbackObj_apply_snd hApp.isLimit a
    have eR_fst (a) : (eR a).1.1 = (pullback.fst f (j.target.left ≫ φ)).app T a :=
      PullbackCone.IsLimit.equivPullbackObj_apply_fst hAppR.isLimit a
    have eR_snd (a) : (eR a).1.2 = (pullback.snd f (j.target.left ≫ φ)).app T a :=
      PullbackCone.IsLimit.equivPullbackObj_apply_snd hAppR.isLimit a
    have hPair : ∀ (m' : (baseChangedArrows j φ f).left ⟶ pullback f φ) (m : R.left ⟶ U.left)
        (r : (baseChangedArrows j φ f).left.obj T),
        m' ≫ pullback.fst f φ = pullback.fst f (j.target.left ≫ φ) →
        m' ≫ pullback.snd f φ = pullback.snd f (j.target.left ≫ φ) ≫ m →
        (eA (m'.app T r)).1 = ((eR r).1.1, m.app T (eR r).1.2) := by
      intro m' m r h₁ h₂
      refine Prod.ext ?_ ?_
      · calc (eA (m'.app T r)).1.1
            = (pullback.fst f φ).app T (m'.app T r) := eA_fst _
          _ = (pullback.fst f (j.target.left ≫ φ)).app T r :=
            congrArg (fun k : pullback f (j.target.left ≫ φ) ⟶ X' ↦ k.app T r) h₁
          _ = (eR r).1.1 := (eR_fst _).symm
      · calc (eA (m'.app T r)).1.2
            = (pullback.snd f φ).app T (m'.app T r) := eA_snd _
          _ = m.app T ((pullback.snd f (j.target.left ≫ φ)).app T r) :=
            congrArg (fun k : pullback f (j.target.left ≫ φ) ⟶ U.left ↦ k.app T r) h₂
          _ = m.app T (eR r).1.2 := congrArg _ (eR_snd r).symm
    have hTargetPair : ∀ r, eA (j'.target.left.app T r) = sGen (eR r) :=
      fun r ↦ Subtype.ext (hPair _ _ r hj'.1.1 hj'.1.2)
    have hSourcePair : ∀ r, eA (j'.source.left.app T r) = tGen (eR r) :=
      fun r ↦ Subtype.ext (hPair _ _ r hj'.2.1 hj'.2.2)
    have hType := isPullback_coequalizer_baseChange_type (j.target.left.app T)
      (j.source.left.app T) (φ.app T) (f.app T) hinvT
    obtain ⟨e, he⟩ := quotientPresheaf_obj_equiv j T.unop
    obtain ⟨e', he'⟩ := quotientPresheaf_obj_equiv j' T.unop
    let eqQ := e.trans (quotEndpointRelEquiv (j.target.left.app T) (j.source.left.app T))
    let eqQ' := e'.trans (quotEndpointRelEquivCoequalizer
      (j'.target.left.app T) (j'.source.left.app T) sGen tGen eA eR hTargetPair hSourcePair)
    have hsurj := surjective_of_equiv_quot e _ he
    have hsurj' := surjective_of_equiv_quot e' _ he'
    have heQ (a) : eqQ (πj.app T a) =
        Quot.mk (Function.Coequalizer.Rel (j.target.left.app T) (j.source.left.app T)) a := by
      change quotEndpointRelEquiv _ _ (e (πj.app T a)) = _
      rw [he]
      rfl
    have heQ' (a) : eqQ' (πj'.app T a) =
        Quot.mk (Function.Coequalizer.Rel sGen tGen) (eA a) := by
      change quotEndpointRelEquivCoequalizer _ _ sGen tGen eA eR hTargetPair hSourcePair
        (e' (πj'.app T a)) = _
      rw [he']
      exact Quot.congr_mk _ _ _
    have hdX (a) : dToX.app T (πj.app T a) = φ.app T a :=
      congrArg (fun m ↦ m.app T a) (coequalizer.π_desc φ hφ)
    have hdX' (a) : dToX'.app T (πj'.app T a) = (pullback.fst f φ).app T a :=
      congrArg (fun m ↦ m.app T a) (coequalizer.π_desc (pullback.fst f φ) hInv')
    have hdQ (a) : dToQ.app T (πj'.app T a) = πj.app T ((pullback.snd f φ).app T a) :=
      congrArg (fun m ↦ m.app T a) (coequalizer.π_desc (pullback.snd f φ ≫ πj) hkToQ)
    refine hType.of_iso' eqQ'.toIso (Iso.refl _) eqQ.toIso (Iso.refl _) ?_ ?_ rfl ?_
    · ext z
      obtain ⟨a, rfl⟩ := hsurj' z
      change Quot.lift _ _ (eqQ' (πj'.app T a)) = dToX'.app T (πj'.app T a)
      rw [heQ', hdX']
      exact eA_fst a
    · ext z
      obtain ⟨a, rfl⟩ := hsurj' z
      change Quot.lift _ _ (eqQ' (πj'.app T a)) = eqQ (dToQ.app T (πj'.app T a))
      rw [heQ', hdQ, heQ]
      exact congrArg (Quot.mk _) (eA_snd a)
    · ext z
      obtain ⟨a, rfl⟩ := hsurj z
      change Quot.lift _ _ (eqQ (πj.app T a)) = dToX.app T (πj.app T a)
      rw [heQ, hdX]
  -- sheafifying it gives the square of quotient sheaves
  let L := presheafToSheaf (BigFppfOver.topology site S hS) (Type u)
  let adj := sheafificationAdjunction (BigFppfOver.topology site S hS) (Type u)
  refine ⟨L.map dToX ≫ adj.counit.app (baseSheaf hX),
    L.map dToX' ≫ adj.counit.app (baseSheaf hX'), L.map dToQ,
    toQuotientSheaf_presheafToSheaf_map_desc j (baseSheaf hX) φ hφ,
    toQuotientSheaf_presheafToSheaf_map_desc j' (baseSheaf hX') (pullback.fst f φ) hInv',
    ?_, ?_⟩
  · calc toQuotientSheaf j' ≫ (L.map dToQ).hom
        = πj' ≫ toSheafify (BigFppfOver.topology site S hS) (quotientPresheaf j') ≫
            sheafifyMap (BigFppfOver.topology site S hS) dToQ := Category.assoc _ _ _
      _ = πj' ≫ dToQ ≫
            toSheafify (BigFppfOver.topology site S hS) (quotientPresheaf j) :=
          congrArg (fun m ↦ πj' ≫ m) (toSheafify_naturality _ dToQ).symm
      _ = (pullback.snd f φ ≫ πj) ≫
            toSheafify (BigFppfOver.topology site S hS) (quotientPresheaf j) :=
          congrArg
            (fun m ↦ m ≫ toSheafify (BigFppfOver.topology site S hS) (quotientPresheaf j))
            (coequalizer.π_desc (pullback.snd f φ ≫ πj) hkToQ)
      _ = pullback.snd f φ ≫ toQuotientSheaf j := Category.assoc _ _ _
  · exact (hPresheaf.map L).of_iso (Iso.refl _) (asIso (adj.counit.app (baseSheaf hX')))
      (Iso.refl _) (asIso (adj.counit.app (baseSheaf hX))) (by simp) (by simp)
      (adj.counit.naturality (show baseSheaf hX' ⟶ baseSheaf hX from ⟨f⟩)) (by simp)

end AlgebraicGeometry.Space

end
