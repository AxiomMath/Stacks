module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantLimit.Constants

/-!
# Faithfulness and fullness for finite locally constant sheaves along a limit of schemes

Let `X = lim X_i` be the limit of a directed inverse system of quasi-compact, quasi-separated
schemes with affine transition morphisms inside a big étale site. This file proves the
faithfulness and the fullness halves of Stacks Tag 0GL2: for two finite locally constant sheaves
`F`, `G` (of sets, of abelian groups, or of finite type of `Λ`-modules) at a stage `X_i`, maps
between their inverse images to `X` come from maps at a later stage, and two maps at `X_i` which
agree on `X` agree at a later stage.

## Strategy

Both sheaves are constant on the members `W_k` of a common finite affine étale covering of `X_i`.
A morphism between the inverse images of `F` and `G` along any `T ⟶ X_i` factoring through `W_k`
is read, through the two trivializations, as a morphism of constant sheaves on `T`
(`AlgebraicGeometry.smallEtaleTrivAlong`), and restriction along `T' ⟶ T` becomes the transport of
morphisms of constant sheaves (`AlgebraicGeometry.smallEtaleTrivAlong_restrict`). Over the member
system `j ↦ W_k ×_{X_i} X_j`, whose limit is `W_k ×_{X_i} X`, the case of constant sheaves
(`AlgebraicGeometry.exists_stage_transport_eq` and
`AlgebraicGeometry.exists_stage_transport_eq_of_transport_eq`) applies:

* *faithfulness*: two maps agreeing on `X` agree on `W_k ×_{X_i} X_j` for late `j`, hence on the
  covering `{W_k ×_{X_i} X_j}` of `X_j`, hence at `X_j`;
* *fullness*: a map on `X` comes over `W_k ×_{X_i} X` from a map over `W_k ×_{X_i} X_{j_k}`; two
  such local maps agree on the overlaps at a late stage (injectivity over the member system of
  `W_k ×_{X_i} W_l`), so they glue at a late stage `X_J`, and the glued map induces the given one
  on `X` since both agree on the covering `{W_k ×_{X_i} X}`.

## Main results

* `AlgebraicGeometry.smallEtaleStagesFaithful_of_isTrivialized` and
  `AlgebraicGeometry.smallEtaleStagesFull_of_isTrivialized` — faithfulness and fullness of the
  comparison for any class of sheaves trivialized with values satisfying a property `P`, for a
  coefficient category in which morphisms of constant sheaves with source satisfying `P` are
  locally constant and the constant sheaf functor is faithful over nonempty schemes.
* `AlgebraicGeometry.smallEtaleStagesFaithful_isFiniteLocallyConstant_type`,
  `AlgebraicGeometry.smallEtaleStagesFull_isFiniteLocallyConstant_type` — clause (1).
* `AlgebraicGeometry.smallEtaleStagesFaithful_isFiniteLocallyConstant_addCommGrpCat`,
  `AlgebraicGeometry.smallEtaleStagesFull_isFiniteLocallyConstant_addCommGrpCat` — clause (2).
* `AlgebraicGeometry.smallEtaleStagesFaithful_isFiniteTypeLocallyConstant`,
  `AlgebraicGeometry.smallEtaleStagesFull_isFiniteTypeLocallyConstant` — clause (3), over an
  arbitrary commutative ring.

## References

* [Stacks Project, Tag 0GL2](https://stacks.math.columbia.edu/tag/0GL2)
* [Stacks Project, Tag 0EYL](https://stacks.math.columbia.edu/tag/0EYL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe t v u

namespace AlgebraicGeometry

section Restriction

variable (B : BigEtaleSite.{u}) (A : Type t) [Category.{v} A]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous A
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]

/-- **Restriction of a morphism between inverse images.** For `f : T' ⟶ T` and `s : T ⟶ R` with a
named composite `f ≫ s = s'`, a morphism between the inverse images of `F` and `G` along `s` is
sent to the morphism between their inverse images along `s'` obtained by inverse image along `f`,
read through the comparisons `AlgebraicGeometry.smallEtaleSheafPullbackCompIso'`. -/
public def smallEtaleHomRestrict {R T T' : B.Scheme} (f : T' ⟶ T) (s : T ⟶ R) (s' : T' ⟶ R)
    (e : f ≫ s = s') {F G : Sheaf (SmallEtale.topology B R.obj R.property) A}
    (x : (smallEtaleSheafPullback B A s).obj F ⟶ (smallEtaleSheafPullback B A s).obj G) :
    (smallEtaleSheafPullback B A s').obj F ⟶ (smallEtaleSheafPullback B A s').obj G :=
  (smallEtaleSheafPullbackCompIso' B A f s s' e).inv.app F ≫
    (smallEtaleSheafPullback B A f).map x ≫
      (smallEtaleSheafPullbackCompIso' B A f s s' e).hom.app G

/-- The restriction of the inverse image of a morphism is its inverse image. -/
public theorem smallEtaleHomRestrict_map {R T T' : B.Scheme} (f : T' ⟶ T) (s : T ⟶ R)
    (s' : T' ⟶ R) (e : f ≫ s = s') {F G : Sheaf (SmallEtale.topology B R.obj R.property) A}
    (x : F ⟶ G) :
    smallEtaleHomRestrict B A f s s' e ((smallEtaleSheafPullback B A s).map x) =
      (smallEtaleSheafPullback B A s').map x := by
  have h := (smallEtaleSheafPullbackCompIso' B A f s s' e).hom.naturality x
  simp only [Functor.comp_map] at h
  rw [smallEtaleHomRestrict, h, Iso.inv_hom_id_app_assoc]

/-- The coherence of the comparisons `AlgebraicGeometry.smallEtaleSheafPullbackCompIso'` for a
triple composite, in the form used to move an inverse image past a comparison. -/
private theorem smallEtaleSheafPullbackCompIso'_inv_app_map_inv_app {R T T' T'' : B.Scheme}
    (f' : T'' ⟶ T') (f : T' ⟶ T) (s : T ⟶ R) (f'' : T'' ⟶ T) (s' : T' ⟶ R) (s'' : T'' ⟶ R)
    (h : f' ≫ f = f'') (e : f ≫ s = s') (e'' : f'' ≫ s = s'') (e' : f' ≫ s' = s'')
    (F : Sheaf (SmallEtale.topology B R.obj R.property) A) :
    (smallEtaleSheafPullbackCompIso' B A f' s' s'' e').inv.app F ≫
        (smallEtaleSheafPullback B A f').map
          ((smallEtaleSheafPullbackCompIso' B A f s s' e).inv.app F) =
      (smallEtaleSheafPullbackCompIso' B A f'' s s'' e'').inv.app F ≫
        (smallEtaleSheafPullbackCompIso' B A f' f f'' h).inv.app
          ((smallEtaleSheafPullback B A s).obj F) := by
  have hi := congrArg Iso.inv (Iso.ext
    (smallEtaleSheafPullbackCompIso'_assoc B A f' f s f'' s' s'' h e e'' e' F) :
    (smallEtaleSheafPullback B A f').mapIso ((smallEtaleSheafPullbackCompIso' B A f s s' e).app F)
        ≪≫ (smallEtaleSheafPullbackCompIso' B A f' s' s'' e').app F =
      (smallEtaleSheafPullbackCompIso' B A f' f f'' h).app
        ((smallEtaleSheafPullback B A s).obj F) ≪≫
        (smallEtaleSheafPullbackCompIso' B A f'' s s'' e'').app F)
  simpa using hi

/-- **Restriction is transitive.** -/
public theorem smallEtaleHomRestrict_restrict {R T T' T'' : B.Scheme} (f : T' ⟶ T)
    (s : T ⟶ R) (s' : T' ⟶ R) (e : f ≫ s = s') (f' : T'' ⟶ T') (s'' : T'' ⟶ R)
    (e' : f' ≫ s' = s'') (f'' : T'' ⟶ T) (e'' : f'' ≫ s = s'') (h : f' ≫ f = f'')
    {F G : Sheaf (SmallEtale.topology B R.obj R.property) A}
    (x : (smallEtaleSheafPullback B A s).obj F ⟶ (smallEtaleSheafPullback B A s).obj G) :
    smallEtaleHomRestrict B A f' s' s'' e' (smallEtaleHomRestrict B A f s s' e x) =
      smallEtaleHomRestrict B A f'' s s'' e'' x := by
  have hG := smallEtaleSheafPullbackCompIso'_assoc B A f' f s f'' s' s'' h e e'' e' G
  have hn := (smallEtaleSheafPullbackCompIso' B A f' f f'' h).hom.naturality x
  simp only [Functor.comp_map] at hn
  simp only [smallEtaleHomRestrict, Functor.map_comp, Category.assoc]
  rw [hG, reassoc_of% (smallEtaleSheafPullbackCompIso'_inv_app_map_inv_app B A f' f s f'' s' s''
    h e e'' e' F), reassoc_of% hn, Iso.inv_hom_id_app_assoc]

/-- Two morphisms have the same restriction along `f` exactly when they have the same inverse
image along `f`. -/
public theorem smallEtaleHomRestrict_eq_iff {R T T' : B.Scheme} (f : T' ⟶ T) (s : T ⟶ R)
    (s' : T' ⟶ R) (e : f ≫ s = s') {F G : Sheaf (SmallEtale.topology B R.obj R.property) A}
    (x y : (smallEtaleSheafPullback B A s).obj F ⟶ (smallEtaleSheafPullback B A s).obj G) :
    smallEtaleHomRestrict B A f s s' e x = smallEtaleHomRestrict B A f s s' e y ↔
      (smallEtaleSheafPullback B A f).map x = (smallEtaleSheafPullback B A f).map y := by
  simp only [smallEtaleHomRestrict, cancel_epi]
  exact cancel_mono _

/-- Two morphisms are equal if they have the same restriction to the base changes of the members
of a covering by objects of the small étale site. -/
private theorem eq_of_smallEtaleHomRestrict_pullback_snd_eq {R S : B.Scheme} (s : S ⟶ R)
    {K : Type (u + 1)} (W : K → SmallEtale B R.obj R.property)
    (hW : Sieve.ofArrows W (fun k => (SmallEtale.finalIsTerminal B R.obj R.property).from (W k)) ∈
      SmallEtale.topology B R.obj R.property (SmallEtale.final B R.obj R.property))
    {F G : Sheaf (SmallEtale.topology B R.obj R.property) A}
    (x y : (smallEtaleSheafPullback B A s).obj F ⟶ (smallEtaleSheafPullback B A s).obj G)
    (h : ∀ k, smallEtaleHomRestrict B A (pullback.snd (W k).obj.hom s) s
        (pullback.fst (W k).obj.hom s ≫ (W k).obj.hom) pullback.condition.symm x =
      smallEtaleHomRestrict B A (pullback.snd (W k).obj.hom s) s
        (pullback.fst (W k).obj.hom s ≫ (W k).obj.hom) pullback.condition.symm y) : x = y :=
  smallEtaleSheafPullback_jointly_faithful B A S
    (SmallEtaleGluing.memberHom B _ fun k => (smallEtaleBaseChange B s).obj (W k))
    (SmallEtaleGluing.sieve_ofEtaleHom_memberHom B _ _
      (smallEtale_sieve_ofArrows_final_baseChange B _ W _ hW))
    x y fun k =>
      (smallEtaleHomRestrict_eq_iff B A _ _ _ pullback.condition.symm x y).mp (h k)

variable [∀ (S : B.Scheme), HasWeakSheafify (SmallEtale.topology B S.obj S.property) A]

/-- **The trivialization induced along a factorization.** If the inverse image of `F` along
`w : W ⟶ R` is the constant sheaf on `E`, then so is its inverse image along any `s : T ⟶ R`
which factors as `u ≫ w = s`. -/
public def smallEtaleTrivAlong {R W T : B.Scheme} {w : W ⟶ R}
    {F : Sheaf (SmallEtale.topology B R.obj R.property) A} {E : A}
    (φ : (smallEtaleSheafPullback B A w).obj F ≅
      (constantSheaf (SmallEtale.topology B W.obj W.property) A).obj E)
    (u : T ⟶ W) (s : T ⟶ R) (e : u ≫ w = s) :
    (smallEtaleSheafPullback B A s).obj F ≅
      (constantSheaf (SmallEtale.topology B T.obj T.property) A).obj E :=
  ((smallEtaleSheafPullbackCompIso' B A u w s e).app F).symm ≪≫
    (smallEtaleSheafPullback B A u).mapIso φ ≪≫ smallEtaleConstantPullbackIso B A u E

/-- **Naturality of the trivializations.** -/
public theorem smallEtaleTrivAlong_hom {R W T T' : B.Scheme} {w : W ⟶ R}
    {F : Sheaf (SmallEtale.topology B R.obj R.property) A} {E : A}
    (φ : (smallEtaleSheafPullback B A w).obj F ≅
      (constantSheaf (SmallEtale.topology B W.obj W.property) A).obj E)
    (u : T ⟶ W) (s : T ⟶ R) (e : u ≫ w = s) (f : T' ⟶ T) (u' : T' ⟶ W) (s' : T' ⟶ R)
    (e' : u' ≫ w = s') (hu : f ≫ u = u') (hs : f ≫ s = s') :
    (smallEtaleTrivAlong B A φ u' s' e').hom =
      (smallEtaleSheafPullbackCompIso' B A f s s' hs).inv.app F ≫
        (smallEtaleSheafPullback B A f).map (smallEtaleTrivAlong B A φ u s e).hom ≫
          (smallEtaleConstantPullbackIso B A f E).hom := by
  have hn := (smallEtaleSheafPullbackCompIso' B A f u u' hu).inv.naturality φ.hom
  simp only [Functor.comp_map] at hn
  have hc := smallEtaleSheafPullbackCompIso'_inv_app_constantSheaf B A f u u' hu E
  simp only [smallEtaleTrivAlong, Iso.trans_hom, Iso.symm_hom, Iso.app_inv,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [reassoc_of% (smallEtaleSheafPullbackCompIso'_inv_app_map_inv_app B A f u w u' s s' hu e e'
    hs F), ← reassoc_of% hn, hc]

/-- **Naturality of the trivializations**, for the inverses. -/
public theorem smallEtaleTrivAlong_inv {R W T T' : B.Scheme} {w : W ⟶ R}
    {F : Sheaf (SmallEtale.topology B R.obj R.property) A} {E : A}
    (φ : (smallEtaleSheafPullback B A w).obj F ≅
      (constantSheaf (SmallEtale.topology B W.obj W.property) A).obj E)
    (u : T ⟶ W) (s : T ⟶ R) (e : u ≫ w = s) (f : T' ⟶ T) (u' : T' ⟶ W) (s' : T' ⟶ R)
    (e' : u' ≫ w = s') (hu : f ≫ u = u') (hs : f ≫ s = s') :
    (smallEtaleTrivAlong B A φ u' s' e').inv =
      (smallEtaleConstantPullbackIso B A f E).inv ≫
        (smallEtaleSheafPullback B A f).map (smallEtaleTrivAlong B A φ u s e).inv ≫
          (smallEtaleSheafPullbackCompIso' B A f s s' hs).hom.app F := by
  rw [← cancel_epi (smallEtaleTrivAlong B A φ u' s' e').hom, Iso.hom_inv_id,
    smallEtaleTrivAlong_hom B A φ u s e f u' s' e' hu hs]
  simp

/-- **Restriction in trivializations is transport.** -/
public theorem smallEtaleTrivAlong_restrict {R W W' T T' : B.Scheme} {w : W ⟶ R}
    {w' : W' ⟶ R} {F G : Sheaf (SmallEtale.topology B R.obj R.property) A} {E E' : A}
    (φ : (smallEtaleSheafPullback B A w).obj F ≅
      (constantSheaf (SmallEtale.topology B W.obj W.property) A).obj E)
    (ψ : (smallEtaleSheafPullback B A w').obj G ≅
      (constantSheaf (SmallEtale.topology B W'.obj W'.property) A).obj E')
    (u : T ⟶ W) (v : T ⟶ W') (s : T ⟶ R) (e : u ≫ w = s) (ev : v ≫ w' = s) (f : T' ⟶ T)
    (u' : T' ⟶ W) (v' : T' ⟶ W') (s' : T' ⟶ R) (e' : u' ≫ w = s') (ev' : v' ≫ w' = s')
    (hu : f ≫ u = u') (hv : f ≫ v = v') (hs : f ≫ s = s')
    (x : (smallEtaleSheafPullback B A s).obj F ⟶ (smallEtaleSheafPullback B A s).obj G) :
    (smallEtaleTrivAlong B A φ u' s' e').inv ≫ smallEtaleHomRestrict B A f s s' hs x ≫
        (smallEtaleTrivAlong B A ψ v' s' ev').hom =
      smallEtaleConstantTransport B A f
        ((smallEtaleTrivAlong B A φ u s e).inv ≫ x ≫ (smallEtaleTrivAlong B A ψ v s ev).hom) := by
  rw [smallEtaleConstantTransport, smallEtaleTrivAlong_inv B A φ u s e f u' s' e' hu hs,
    smallEtaleTrivAlong_hom B A ψ v s ev f v' s' ev' hv hs]
  simp [smallEtaleHomRestrict]

/-- The inverse image of a morphism along a factorization through `w`, read in the induced
trivializations, is the transport of the morphism read in the trivializations over `w`. -/
public theorem smallEtaleTrivAlong_map {R W T : B.Scheme} {w : W ⟶ R}
    {F G : Sheaf (SmallEtale.topology B R.obj R.property) A} {E E' : A}
    (φ : (smallEtaleSheafPullback B A w).obj F ≅
      (constantSheaf (SmallEtale.topology B W.obj W.property) A).obj E)
    (ψ : (smallEtaleSheafPullback B A w).obj G ≅
      (constantSheaf (SmallEtale.topology B W.obj W.property) A).obj E')
    (u : T ⟶ W) (s : T ⟶ R) (e : u ≫ w = s) (a : F ⟶ G) :
    (smallEtaleTrivAlong B A φ u s e).inv ≫ (smallEtaleSheafPullback B A s).map a ≫
        (smallEtaleTrivAlong B A ψ u s e).hom =
      smallEtaleConstantTransport B A u
        (φ.inv ≫ (smallEtaleSheafPullback B A w).map a ≫ ψ.hom) := by
  rw [← smallEtaleHomRestrict_map B A u w s e a]
  simp [smallEtaleTrivAlong, smallEtaleHomRestrict, smallEtaleConstantTransport]

/-- The inverse of restriction along `v`, for a morphism between inverse images along a named
composite `v ≫ s = sk`. -/
public def smallEtaleHomUnrestrict {R S T : B.Scheme} (v : T ⟶ S) (s : S ⟶ R) (sk : T ⟶ R)
    (ek : v ≫ s = sk) {F G : Sheaf (SmallEtale.topology B R.obj R.property) A}
    (z : (smallEtaleSheafPullback B A sk).obj F ⟶ (smallEtaleSheafPullback B A sk).obj G) :
    (smallEtaleSheafPullback B A v).obj ((smallEtaleSheafPullback B A s).obj F) ⟶
      (smallEtaleSheafPullback B A v).obj ((smallEtaleSheafPullback B A s).obj G) :=
  (smallEtaleSheafPullbackCompIso' B A v s sk ek).hom.app F ≫ z ≫
    (smallEtaleSheafPullbackCompIso' B A v s sk ek).inv.app G

omit [∀ (S : B.Scheme), HasWeakSheafify (SmallEtale.topology B S.obj S.property) A] in
/-- **Restriction of an unrestricted morphism.** Restricting along `p` the morphism
`AlgebraicGeometry.smallEtaleHomUnrestrict` attached to `z` is restricting `z` along `p`, up to
the comparison for the composite `o ≫ s`. -/
public theorem smallEtaleHomRestrict_conj {R S T T' : B.Scheme} (s : S ⟶ R) (v : T ⟶ S)
    (sk : T ⟶ R) (ek : v ≫ s = sk) (p : T' ⟶ T) (o : T' ⟶ S) (eo : p ≫ v = o)
    (e : p ≫ sk = o ≫ s) {F G : Sheaf (SmallEtale.topology B R.obj R.property) A}
    (z : (smallEtaleSheafPullback B A sk).obj F ⟶ (smallEtaleSheafPullback B A sk).obj G) :
    (smallEtaleSheafPullbackCompIso' B A p v o eo).inv.app ((smallEtaleSheafPullback B A s).obj F) ≫
        (smallEtaleSheafPullback B A p).map (smallEtaleHomUnrestrict B A v s sk ek z) ≫
        (smallEtaleSheafPullbackCompIso' B A p v o eo).hom.app
          ((smallEtaleSheafPullback B A s).obj G) =
      (smallEtaleSheafPullbackCompIso' B A o s (o ≫ s) rfl).hom.app F ≫
        smallEtaleHomRestrict B A p sk (o ≫ s) e z ≫
          (smallEtaleSheafPullbackCompIso' B A o s (o ≫ s) rfl).inv.app G := by
  have h1 : ∀ X, (smallEtaleSheafPullbackCompIso' B A p v o eo).inv.app
        ((smallEtaleSheafPullback B A s).obj X) ≫
        (smallEtaleSheafPullback B A p).map
          ((smallEtaleSheafPullbackCompIso' B A v s sk ek).hom.app X) =
      (smallEtaleSheafPullbackCompIso' B A o s (o ≫ s) rfl).hom.app X ≫
        (smallEtaleSheafPullbackCompIso' B A p sk (o ≫ s) e).inv.app X := fun X => by
    rw [← cancel_mono ((smallEtaleSheafPullbackCompIso' B A p sk (o ≫ s) e).hom.app X),
      Category.assoc, Category.assoc,
      smallEtaleSheafPullbackCompIso'_assoc B A p v s o sk (o ≫ s) eo ek rfl e X,
      Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app, Category.comp_id]
  have h2 : ∀ X, (smallEtaleSheafPullback B A p).map
        ((smallEtaleSheafPullbackCompIso' B A v s sk ek).inv.app X) ≫
        (smallEtaleSheafPullbackCompIso' B A p v o eo).hom.app
          ((smallEtaleSheafPullback B A s).obj X) =
      (smallEtaleSheafPullbackCompIso' B A p sk (o ≫ s) e).hom.app X ≫
        (smallEtaleSheafPullbackCompIso' B A o s (o ≫ s) rfl).inv.app X := fun X => by
    have hi := congrArg Iso.inv (Iso.ext (h1 X) :
      ((smallEtaleSheafPullbackCompIso' B A p v o eo).app
          ((smallEtaleSheafPullback B A s).obj X)).symm ≪≫
        (smallEtaleSheafPullback B A p).mapIso
          ((smallEtaleSheafPullbackCompIso' B A v s sk ek).app X) =
      (smallEtaleSheafPullbackCompIso' B A o s (o ≫ s) rfl).app X ≪≫
        ((smallEtaleSheafPullbackCompIso' B A p sk (o ≫ s) e).app X).symm)
    simpa using hi
  simp only [smallEtaleHomUnrestrict, Functor.map_comp, Category.assoc]
  rw [reassoc_of% h1 F, h2 G]
  simp only [smallEtaleHomRestrict, Category.assoc]

section Gluing

open SmallEtaleGluing

omit [∀ (S : B.Scheme), HasWeakSheafify (SmallEtale.topology B S.obj S.property) A] in
/-- **Restrictions to the members of an étale covering are jointly faithful.** -/
public theorem smallEtaleHomRestrict_jointly_faithful {R S : B.Scheme} (s : S ⟶ R) {ι : Type*}
    {X : ι → B.Scheme} (f : ∀ k, X k ⟶ S) [∀ k, Etale (B.inclusion.map (f k))]
    (hf : Sieve.ofArrows (fun k => SmallEtale.ofEtaleHom B (f k))
      (fun _ => (SmallEtale.finalIsTerminal B S.obj S.property).from _) ∈
        SmallEtale.topology B S.obj S.property (SmallEtale.final B S.obj S.property))
    (sk : ∀ k, X k ⟶ R) (ek : ∀ k, f k ≫ s = sk k)
    {F G : Sheaf (SmallEtale.topology B R.obj R.property) A}
    (x y : (smallEtaleSheafPullback B A s).obj F ⟶ (smallEtaleSheafPullback B A s).obj G)
    (h : ∀ k, smallEtaleHomRestrict B A (f k) s (sk k) (ek k) x =
      smallEtaleHomRestrict B A (f k) s (sk k) (ek k) y) : x = y :=
  smallEtaleSheafPullback_jointly_faithful B A S f hf x y fun k =>
    (smallEtaleHomRestrict_eq_iff B A _ _ _ (ek k) x y).mp (h k)

omit [∀ (S : B.Scheme), HasWeakSheafify (SmallEtale.topology B S.obj S.property) A] in
/-- **Restrictions glue along an étale covering.** Morphisms over the members of an étale
covering of `S`, between the inverse images of two sheaves on `R` along the composites with
`s : S ⟶ R`, whose restrictions to the overlaps agree, are the restrictions of a morphism over
`S`. -/
public theorem smallEtaleHomRestrict_glue {R S : B.Scheme} (s : S ⟶ R) {ι : Type*}
    {X : ι → B.Scheme} (f : ∀ k, X k ⟶ S) [∀ k, Etale (B.inclusion.map (f k))]
    (hf : Sieve.ofArrows (fun k => SmallEtale.ofEtaleHom B (f k))
      (fun _ => (SmallEtale.finalIsTerminal B S.obj S.property).from _) ∈
        SmallEtale.topology B S.obj S.property (SmallEtale.final B S.obj S.property))
    (O : ι → ι → B.Scheme) (p : ∀ k l, O k l ⟶ X k) (q : ∀ k l, O k l ⟶ X l)
    (r : ∀ k l, O k l ⟶ S) (hO : ∀ k l, IsPullback (p k l) (q k l) (f k) (f l))
    (hr₁ : ∀ k l, p k l ≫ f k = r k l) (hr₂ : ∀ k l, q k l ≫ f l = r k l)
    (sk : ∀ k, X k ⟶ R) (ek : ∀ k, f k ≫ s = sk k)
    {F G : Sheaf (SmallEtale.topology B R.obj R.property) A}
    (z : ∀ k, (smallEtaleSheafPullback B A (sk k)).obj F ⟶
      (smallEtaleSheafPullback B A (sk k)).obj G)
    (hz : ∀ k l (e₁ : p k l ≫ sk k = r k l ≫ s) (e₂ : q k l ≫ sk l = r k l ≫ s),
      smallEtaleHomRestrict B A (p k l) (sk k) _ e₁ (z k) =
        smallEtaleHomRestrict B A (q k l) (sk l) _ e₂ (z l)) :
    ∃ x : (smallEtaleSheafPullback B A s).obj F ⟶ (smallEtaleSheafPullback B A s).obj G,
      ∀ k, smallEtaleHomRestrict B A (f k) s (sk k) (ek k) x = z k := by
  obtain ⟨ψ, hψ⟩ := smallEtaleSheafPullback_exists_map_eq_of_isPullback B A S f hf O p q r hO
    hr₁ hr₂ (fun k => smallEtaleHomUnrestrict B A (f k) s (sk k) (ek k) (z k))
    (fun k l => (smallEtaleHomRestrict_conj B A s _ _ (ek k) (p k l) _ (hr₁ k l)
          (by rw [← ek k, ← hr₁ k l, Category.assoc]) (z k)).trans
        ((congrArg (fun w => _ ≫ w ≫ _) (hz k l _ _)).trans
          (smallEtaleHomRestrict_conj B A s _ _ (ek l) (q k l) _ (hr₂ k l)
          (by rw [← ek l, ← hr₂ k l, Category.assoc]) (z l)).symm))
  refine ⟨ψ, fun k => ?_⟩
  simp [smallEtaleHomRestrict, hψ k, smallEtaleHomUnrestrict]

end Gluing

end Restriction

section Stages

variable (B : BigEtaleSite.{u}) (A : Type t) [Category.{v} A]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous A
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  {I : Type*} [Preorder I] (Dg : Iᵒᵖ ⥤ B.Scheme) (c : Cone (Dg ⋙ B.inclusion))
  (hX : B.Contains c.pt)

/-- The stage comparison is the comparison along the cone equation. -/
public theorem smallEtaleStageComparison_eq {i j : I} (h : i ≤ j)
    (F : Sheaf (SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property) A) :
    smallEtaleStageComparison B A Dg c hX h F =
      (smallEtaleSheafPullbackCompIso' B A (coneStageHom B Dg c hX j) (systemStageHom B Dg h)
        (coneStageHom B Dg c hX i) (coneStageHom_comp B Dg c hX h)).app F := by
  ext1
  simp [smallEtaleStageComparison, smallEtaleSheafPullbackStageComparison,
    smallEtaleSheafPullbackCompIso', eqToHom_app]

end Stages

section Trivializing

variable (B : BigEtaleSite.{u}) (A : Type t) [Category.{v} A]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous A
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (X : B.Scheme) (V : SmallEtale B X.obj X.property),
    HasWeakSheafify ((SmallEtale.topology B X.obj X.property).over V) A]

/-- **The trivializing sieve.** The sieve of objects `W` of the small étale site of `S` over which
the inverse image of `F` is a constant sheaf with value satisfying `P`. -/
public def smallEtaleTrivializingSieve (P : A → Prop) {S : B.Scheme}
    (F : Sheaf (SmallEtale.topology B S.obj S.property) A) :
    Sieve (SmallEtale.final B S.obj S.property) where
  arrows W _ := ∃ E : A, P E ∧ Nonempty ((smallEtaleSheafPullback B A W.obj.hom).obj F ≅
    (constantSheaf (SmallEtale.topology B W.obj.left.obj W.obj.left.property) A).obj E)
  downward_closed {W W'} _ := by
    rintro ⟨E, hE, ⟨φ⟩⟩ q
    exact ⟨E, hE, ⟨smallEtaleTrivAlong B A φ q.hom.left W'.obj.hom (Over.w q.hom)⟩⟩

/-- A trivialized sheaf has a covering trivializing sieve. -/
public theorem smallEtaleTrivializingSieve_mem (P : A → Prop) {S : B.Scheme}
    (F : Sheaf (SmallEtale.topology B S.obj S.property) A)
    (hF : IsTrivializedSmallEtaleSheaf B A P S F) :
    smallEtaleTrivializingSieve B A P F ∈
      SmallEtale.topology B S.obj S.property (SmallEtale.final B S.obj S.property) := by
  obtain ⟨K, V, g, hV, h⟩ := hF (SmallEtale.final B S.obj S.property)
  refine (SmallEtale.topology B S.obj S.property).superset_covering ?_ hV
  rw [Sieve.ofArrows, Sieve.generate_le_iff]
  rintro _ _ ⟨k⟩
  obtain ⟨E, hE, hiso⟩ := h k
  obtain ⟨φ⟩ := (nonempty_constantSheafIso_over_iff B S.obj S.property (V k) A F E).mp hiso
  exact ⟨E, hE, ⟨φ.symm⟩⟩

/-- **Two trivialized sheaves on a quasi-compact, quasi-separated scheme are trivialized on a
common finite affine covering.** -/
public theorem exists_finite_affine_trivializing (P : A → Prop) (S : B.Scheme)
    [CompactSpace S.obj] [QuasiSeparatedSpace S.obj]
    (F G : Sheaf (SmallEtale.topology B S.obj S.property) A)
    (hF : IsTrivializedSmallEtaleSheaf B A P S F) (hG : IsTrivializedSmallEtaleSheaf B A P S G) :
    ∃ (K : Type (u + 1)) (_ : Finite K) (W : K → SmallEtale B S.obj S.property),
      Sieve.ofArrows W (fun k => (SmallEtale.finalIsTerminal B S.obj S.property).from (W k)) ∈
        SmallEtale.topology B S.obj S.property (SmallEtale.final B S.obj S.property) ∧
      (∀ k, IsAffine (W k).obj.left.obj) ∧
      ∀ k, (∃ E : A, P E ∧ Nonempty ((smallEtaleSheafPullback B A (W k).obj.hom).obj F ≅
          (constantSheaf (SmallEtale.topology B (W k).obj.left.obj
            (W k).obj.left.property) A).obj E)) ∧
        (∃ E : A, P E ∧ Nonempty ((smallEtaleSheafPullback B A (W k).obj.hom).obj G ≅
          (constantSheaf (SmallEtale.topology B (W k).obj.left.obj
            (W k).obj.left.property) A).obj E)) :=
  exists_finite_affine_le_sieve B S _
    ((SmallEtale.topology B S.obj S.property).intersection_covering
      (smallEtaleTrivializingSieve_mem B A P F hF) (smallEtaleTrivializingSieve_mem B A P G hG))

end Trivializing

section Pullback

variable (B : BigEtaleSite.{u})

/-- A fibre product of quasi-compact, quasi-separated schemes over a quasi-separated scheme is
quasi-compact and quasi-separated. -/
public theorem compactSpace_quasiSeparatedSpace_bigEtalePullback {S Y₁ Y₂ : B.Scheme} (f₁ : Y₁ ⟶ S)
    (f₂ : Y₂ ⟶ S) [QuasiSeparatedSpace S.obj] [CompactSpace Y₁.obj] [QuasiSeparatedSpace Y₁.obj]
    [CompactSpace Y₂.obj] [QuasiSeparatedSpace Y₂.obj] :
    CompactSpace (pullback f₁ f₂).obj ∧ QuasiSeparatedSpace (pullback f₁ f₂).obj := by
  have : CompactSpace (B.inclusion.obj Y₂) := ‹CompactSpace Y₂.obj›
  have : QuasiSeparatedSpace (B.inclusion.obj Y₂) := ‹QuasiSeparatedSpace Y₂.obj›
  have : CompactSpace (B.inclusion.obj Y₁) := ‹CompactSpace Y₁.obj›
  have : QuasiSeparatedSpace (B.inclusion.obj Y₁) := ‹QuasiSeparatedSpace Y₁.obj›
  have : QuasiSeparatedSpace (B.inclusion.obj S) := ‹QuasiSeparatedSpace S.obj›
  have : QuasiCompact (B.inclusion.map (pullback.fst f₁ f₂)) :=
    MorphismProperty.of_isPullback ((IsPullback.of_hasPullback f₁ f₂).map B.inclusion).flip
      (inferInstance : QuasiCompact (B.inclusion.map f₂))
  have : QuasiSeparated (B.inclusion.map (pullback.fst f₁ f₂)) :=
    MorphismProperty.of_isPullback ((IsPullback.of_hasPullback f₁ f₂).map B.inclusion).flip
      (inferInstance : QuasiSeparated (B.inclusion.map f₂))
  exact ⟨QuasiCompact.compactSpace_of_compactSpace (B.inclusion.map (pullback.fst f₁ f₂)),
    quasiSeparatedSpace_of_quasiSeparated (B.inclusion.map (pullback.fst f₁ f₂))⟩

end Pullback

section Overlap

variable (B : BigEtaleSite.{u})

/-- The overlap `W₁ ×_S W₂` of two objects of the small étale site of `S`, as an object of that
site through the first projection. -/
public abbrev smallEtaleMemberOverlap {S : B.Scheme} (W₁ W₂ : SmallEtale B S.obj S.property) :
    SmallEtale B S.obj S.property :=
  ⟨Over.mk (pullback.fst W₁.obj.hom W₂.obj.hom ≫ W₁.obj.hom), by
    have : Etale (B.inclusion.map (pullback.fst W₁.obj.hom W₂.obj.hom)) :=
      MorphismProperty.of_isPullback ((IsPullback.of_hasPullback W₁.obj.hom W₂.obj.hom).map
        B.inclusion).flip W₂.property
    have : Etale (B.inclusion.map W₁.obj.hom) := W₁.property
    change Etale (B.inclusion.map (pullback.fst W₁.obj.hom W₂.obj.hom ≫ W₁.obj.hom))
    rw [B.inclusion.map_comp]
    infer_instance⟩

end Overlap

section Members

variable (B : BigEtaleSite.{u}) {A : Type t} [Category.{v} A]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous A
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (S : B.Scheme), HasWeakSheafify (SmallEtale.topology B S.obj S.property) A]
  {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (Dg : Iᵒᵖ ⥤ B.Scheme) (c : Cone (Dg ⋙ B.inclusion)) (hX : B.Contains c.pt)

/-- **Faithfulness over one member.** If two morphisms between sheaves at the stage `i`,
trivialized over a quasi-compact, quasi-separated `W` with value satisfying `P`, agree after
inverse image to the vertex, then they agree after inverse image to `W ×_{X_i} X_J` for all late
`J`. -/
public theorem exists_stage_map_eq_member (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (P : A → Prop) (hloc : SmallEtaleConstantMapsLocallyConstant B A P)
    (hinj : SmallEtaleConstantFaithful B A) (i : I)
    (W : SmallEtale B (Dg.obj (op i)).obj (Dg.obj (op i)).property)
    [hWc : CompactSpace W.obj.left.obj] [hWq : QuasiSeparatedSpace W.obj.left.obj]
    {F G : Sheaf (SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property) A}
    {E E' : A} (hE : P E)
    (φ : (smallEtaleSheafPullback B A W.obj.hom).obj F ≅
      (constantSheaf (SmallEtale.topology B W.obj.left.obj W.obj.left.property) A).obj E)
    (ψ : (smallEtaleSheafPullback B A W.obj.hom).obj G ≅
      (constantSheaf (SmallEtale.topology B W.obj.left.obj W.obj.left.property) A).obj E')
    (a b : F ⟶ G)
    (hab : (smallEtaleSheafPullback B A (coneStageHom B Dg c hX i)).map a =
      (smallEtaleSheafPullback B A (coneStageHom B Dg c hX i)).map b) :
    ∃ j, i ≤ j ∧ ∀ (J : I) (h : i ≤ J), j ≤ J →
      (smallEtaleSheafPullback B A
          (pullback.fst W.obj.hom (systemStageHom B Dg h) ≫ W.obj.hom)).map a =
        (smallEtaleSheafPullback B A
          (pullback.fst W.obj.hom (systemStageHom B Dg h) ≫ W.obj.hom)).map b := by
  -- the two morphisms read in the trivializations over `W`
  have key : ∀ {T : B.Scheme} (u : T ⟶ W.obj.left),
      (smallEtaleSheafPullback B A (u ≫ W.obj.hom)).map a =
          (smallEtaleSheafPullback B A (u ≫ W.obj.hom)).map b ↔
        smallEtaleConstantTransport B A u
            (φ.inv ≫ (smallEtaleSheafPullback B A W.obj.hom).map a ≫ ψ.hom) =
          smallEtaleConstantTransport B A u
            (φ.inv ≫ (smallEtaleSheafPullback B A W.obj.hom).map b ≫ ψ.hom) := by
    intro T u
    rw [← smallEtaleTrivAlong_map B A φ ψ u _ rfl a, ← smallEtaleTrivAlong_map B A φ ψ u _ rfl b]
    exact ⟨fun h => by rw [h], fun h => (cancel_mono _).mp ((cancel_epi _).mp h)⟩
  have hX' : smallEtaleConstantTransport B A
      (memberConeHom B Dg c hX i W ⟨i, le_rfl⟩)
      (smallEtaleConstantTransport B A (pullback.fst W.obj.hom (systemStageHom B Dg (le_refl i)))
        (φ.inv ≫ (smallEtaleSheafPullback B A W.obj.hom).map a ≫ ψ.hom)) =
      smallEtaleConstantTransport B A
      (memberConeHom B Dg c hX i W ⟨i, le_rfl⟩)
      (smallEtaleConstantTransport B A (pullback.fst W.obj.hom (systemStageHom B Dg (le_refl i)))
        (φ.inv ≫ (smallEtaleSheafPullback B A W.obj.hom).map b ≫ ψ.hom)) := by
    rw [← smallEtaleConstantTransport_comp' B A _ _ _ (memberConeHom_fst B Dg c hX i W _),
      ← smallEtaleConstantTransport_comp' B A _ _ _ (memberConeHom_fst B Dg c hX i W _),
      ← key, ← smallEtaleHomRestrict_map B A (pullback.snd W.obj.hom (coneStageHom B Dg c hX i))
        (coneStageHom B Dg c hX i) _ pullback.condition.symm a,
      ← smallEtaleHomRestrict_map B A (pullback.snd W.obj.hom (coneStageHom B Dg c hX i))
        (coneStageHom B Dg c hX i) _ pullback.condition.symm b, hab]
  obtain ⟨j, hj, hj'⟩ := exists_stage_transport_eq_of_transport_eq B (memberSystem B Dg i W)
    (memberCone B Dg c hX i W) (memberCone_contains B Dg c hX i W)
    (memberConeIsLimit B Dg c hX i W hc) (memberSystem_isAffineHom haff)
    (memberSystem_compactSpace haff hWc) (memberSystem_quasiSeparatedSpace haff hWq) P hloc hinj
    ⟨i, le_rfl⟩ hE _ _ hX'
  refine ⟨j.1, j.2, fun J h hjJ => (key _).mpr ?_⟩
  have hfst : memberSystemHom B Dg i W (show j ≤ ⟨J, h⟩ from hjJ) ≫
      memberSystemHom B Dg i W hj ≫ pullback.fst W.obj.hom (systemStageHom B Dg (le_refl i)) =
      pullback.fst W.obj.hom (systemStageHom B Dg h) := by
    simp
  rw [smallEtaleConstantTransport_comp' B A _ _ _ hfst,
    smallEtaleConstantTransport_comp' B A _ _ _ hfst,
    smallEtaleConstantTransport_comp' B A (memberSystemHom B Dg i W hj) _ _ rfl,
    smallEtaleConstantTransport_comp' B A (memberSystemHom B Dg i W hj) _ _ rfl]
  exact congrArg (smallEtaleConstantTransport B A _) hj'

/-- **Fullness over one member.** A morphism between the inverse images to the vertex of two
sheaves at the stage `i`, trivialized over a quasi-compact, quasi-separated `W` with value
satisfying `P`, agrees over `W ×_{X_i} X` with the restriction of a morphism over
`W ×_{X_i} X_j` for some stage `j`. -/
public theorem exists_stage_restrict_eq_member (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (P : A → Prop) (hloc : SmallEtaleConstantMapsLocallyConstant B A P)
    (hinj : SmallEtaleConstantFaithful B A) (i : I)
    (W : SmallEtale B (Dg.obj (op i)).obj (Dg.obj (op i)).property)
    [hWc : CompactSpace W.obj.left.obj] [hWq : QuasiSeparatedSpace W.obj.left.obj]
    {F G : Sheaf (SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property) A}
    {E E' : A} (hE : P E)
    (φ : (smallEtaleSheafPullback B A W.obj.hom).obj F ≅
      (constantSheaf (SmallEtale.topology B W.obj.left.obj W.obj.left.property) A).obj E)
    (ψ : (smallEtaleSheafPullback B A W.obj.hom).obj G ≅
      (constantSheaf (SmallEtale.topology B W.obj.left.obj W.obj.left.property) A).obj E')
    (a : (smallEtaleSheafPullback B A (coneStageHom B Dg c hX i)).obj F ⟶
      (smallEtaleSheafPullback B A (coneStageHom B Dg c hX i)).obj G) :
    ∃ (j : I) (h : i ≤ j)
      (y : (smallEtaleSheafPullback B A
          (pullback.fst W.obj.hom (systemStageHom B Dg h) ≫ W.obj.hom)).obj F ⟶
        (smallEtaleSheafPullback B A
          (pullback.fst W.obj.hom (systemStageHom B Dg h) ≫ W.obj.hom)).obj G),
      smallEtaleHomRestrict B A (memberConeHom B Dg c hX i W ⟨j, h⟩)
          (pullback.fst W.obj.hom (systemStageHom B Dg h) ≫ W.obj.hom)
          (pullback.fst W.obj.hom (coneStageHom B Dg c hX i) ≫ W.obj.hom)
          (memberConeHom_fst_assoc B Dg c hX i W ⟨j, h⟩ W.obj.hom) y =
        smallEtaleHomRestrict B A (pullback.snd W.obj.hom (coneStageHom B Dg c hX i))
          (coneStageHom B Dg c hX i)
          (pullback.fst W.obj.hom (coneStageHom B Dg c hX i) ≫ W.obj.hom)
          pullback.condition.symm a := by
  set x := smallEtaleHomRestrict B A (pullback.snd W.obj.hom (coneStageHom B Dg c hX i))
    (coneStageHom B Dg c hX i) (pullback.fst W.obj.hom (coneStageHom B Dg c hX i) ≫ W.obj.hom)
    pullback.condition.symm a with hx
  obtain ⟨j, hj, b, hb⟩ := exists_stage_transport_eq B (memberSystem B Dg i W)
    (memberCone B Dg c hX i W) (memberCone_contains B Dg c hX i W)
    (memberConeIsLimit B Dg c hX i W hc) (memberSystem_isAffineHom haff)
    (memberSystem_compactSpace haff hWc) (memberSystem_quasiSeparatedSpace haff hWq) P hloc hinj
    hE ((smallEtaleTrivAlong B A φ (pullback.fst W.obj.hom (coneStageHom B Dg c hX i)) _ rfl).inv ≫
      x ≫ (smallEtaleTrivAlong B A ψ (pullback.fst W.obj.hom (coneStageHom B Dg c hX i)) _ rfl).hom)
    ⟨i, le_rfl⟩
  refine ⟨j.1, j.2,
    (smallEtaleTrivAlong B A φ (pullback.fst W.obj.hom (systemStageHom B Dg j.2)) _ rfl).hom ≫ b ≫
      (smallEtaleTrivAlong B A ψ (pullback.fst W.obj.hom (systemStageHom B Dg j.2)) _ rfl).inv,
    ?_⟩
  have h := smallEtaleTrivAlong_restrict B A φ ψ _ _ _ rfl rfl
    (memberConeHom B Dg c hX i W j) _ _ _ rfl rfl (memberConeHom_fst B Dg c hX i W j)
    (memberConeHom_fst B Dg c hX i W j) (memberConeHom_fst_assoc B Dg c hX i W j W.obj.hom)
    ((smallEtaleTrivAlong B A φ (pullback.fst W.obj.hom (systemStageHom B Dg j.2)) _ rfl).hom ≫ b ≫
      (smallEtaleTrivAlong B A ψ (pullback.fst W.obj.hom (systemStageHom B Dg j.2)) _ rfl).inv)
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc] at h
  have hb' : smallEtaleConstantTransport B A (memberConeHom B Dg c hX i W j) b = _ := hb
  rw [hb'] at h
  rw [← cancel_epi (smallEtaleTrivAlong B A φ
      (pullback.fst W.obj.hom (coneStageHom B Dg c hX i)) _ rfl).inv,
    ← cancel_mono (smallEtaleTrivAlong B A ψ
      (pullback.fst W.obj.hom (coneStageHom B Dg c hX i)) _ rfl).hom]
  simpa only [Category.assoc] using h


/-- **Compatibility over an overlap.** Let `y₁`, `y₂` be morphisms over `W₁ ×_{X_i} X_{j₁}` and
`W₂ ×_{X_i} X_{j₂}` between the inverse images of two sheaves at the stage `i`, both agreeing over
the base change to the vertex with the restriction of the same morphism `a` there. If `F` is
trivialized over `W₁` and `G` over `W₂`, with value of `F` satisfying `P`, and the fibre product
`W₁₂ = W₁ ×_{X_i} W₂` is quasi-compact and quasi-separated, then `y₁` and `y₂` agree on every
scheme mapping compatibly to both over a sufficiently late stage. -/
public theorem exists_stage_restrict_eq_overlap (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (P : A → Prop) (hloc : SmallEtaleConstantMapsLocallyConstant B A P)
    (hinj : SmallEtaleConstantFaithful B A) (i : I)
    (W₁ W₂ W₁₂ : SmallEtale B (Dg.obj (op i)).obj (Dg.obj (op i)).property)
    (pr₁ : W₁₂.obj.left ⟶ W₁.obj.left) (pr₂ : W₁₂.obj.left ⟶ W₂.obj.left)
    (hpb : IsPullback pr₁ pr₂ W₁.obj.hom W₂.obj.hom) (h₁₂ : pr₁ ≫ W₁.obj.hom = W₁₂.obj.hom)
    [hWc : CompactSpace W₁₂.obj.left.obj] [hWq : QuasiSeparatedSpace W₁₂.obj.left.obj]
    {F G : Sheaf (SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property) A}
    {E₁ E₂ : A} (hE : P E₁)
    (φ₁ : (smallEtaleSheafPullback B A W₁.obj.hom).obj F ≅
      (constantSheaf (SmallEtale.topology B W₁.obj.left.obj W₁.obj.left.property) A).obj E₁)
    (ψ₂ : (smallEtaleSheafPullback B A W₂.obj.hom).obj G ≅
      (constantSheaf (SmallEtale.topology B W₂.obj.left.obj W₂.obj.left.property) A).obj E₂)
    (a : (smallEtaleSheafPullback B A (coneStageHom B Dg c hX i)).obj F ⟶
      (smallEtaleSheafPullback B A (coneStageHom B Dg c hX i)).obj G)
    {j₁ j₂ : I} (h₁ : i ≤ j₁) (h₂ : i ≤ j₂)
    (y₁ : (smallEtaleSheafPullback B A
        (pullback.fst W₁.obj.hom (systemStageHom B Dg h₁) ≫ W₁.obj.hom)).obj F ⟶
      (smallEtaleSheafPullback B A
        (pullback.fst W₁.obj.hom (systemStageHom B Dg h₁) ≫ W₁.obj.hom)).obj G)
    (y₂ : (smallEtaleSheafPullback B A
        (pullback.fst W₂.obj.hom (systemStageHom B Dg h₂) ≫ W₂.obj.hom)).obj F ⟶
      (smallEtaleSheafPullback B A
        (pullback.fst W₂.obj.hom (systemStageHom B Dg h₂) ≫ W₂.obj.hom)).obj G)
    (hy₁ : smallEtaleHomRestrict B A (memberConeHom B Dg c hX i W₁ ⟨j₁, h₁⟩)
        (pullback.fst W₁.obj.hom (systemStageHom B Dg h₁) ≫ W₁.obj.hom)
        (pullback.fst W₁.obj.hom (coneStageHom B Dg c hX i) ≫ W₁.obj.hom)
        (memberConeHom_fst_assoc B Dg c hX i W₁ ⟨j₁, h₁⟩ W₁.obj.hom) y₁ =
      smallEtaleHomRestrict B A (pullback.snd W₁.obj.hom (coneStageHom B Dg c hX i))
        (coneStageHom B Dg c hX i)
        (pullback.fst W₁.obj.hom (coneStageHom B Dg c hX i) ≫ W₁.obj.hom)
        pullback.condition.symm a)
    (hy₂ : smallEtaleHomRestrict B A (memberConeHom B Dg c hX i W₂ ⟨j₂, h₂⟩)
        (pullback.fst W₂.obj.hom (systemStageHom B Dg h₂) ≫ W₂.obj.hom)
        (pullback.fst W₂.obj.hom (coneStageHom B Dg c hX i) ≫ W₂.obj.hom)
        (memberConeHom_fst_assoc B Dg c hX i W₂ ⟨j₂, h₂⟩ W₂.obj.hom) y₂ =
      smallEtaleHomRestrict B A (pullback.snd W₂.obj.hom (coneStageHom B Dg c hX i))
        (coneStageHom B Dg c hX i)
        (pullback.fst W₂.obj.hom (coneStageHom B Dg c hX i) ≫ W₂.obj.hom)
        pullback.condition.symm a) :
    ∃ J₀, ∃ (hj₁ : j₁ ≤ J₀) (hj₂ : j₂ ≤ J₀), ∀ (J : I) (hJ : J₀ ≤ J) {T : B.Scheme}
      (g₁ : T ⟶ pullback W₁.obj.hom (systemStageHom B Dg h₁))
      (g₂ : T ⟶ pullback W₂.obj.hom (systemStageHom B Dg h₂)) (v : T ⟶ Dg.obj (op J))
      (_ : g₁ ≫ pullback.snd _ _ = v ≫ systemStageHom B Dg (hj₁.trans hJ))
      (_ : g₂ ≫ pullback.snd _ _ = v ≫ systemStageHom B Dg (hj₂.trans hJ))
      (sT : T ⟶ Dg.obj (op i))
      (e₁ : g₁ ≫ pullback.fst W₁.obj.hom (systemStageHom B Dg h₁) ≫ W₁.obj.hom = sT)
      (e₂ : g₂ ≫ pullback.fst W₂.obj.hom (systemStageHom B Dg h₂) ≫ W₂.obj.hom = sT),
      smallEtaleHomRestrict B A g₁ _ sT e₁ y₁ = smallEtaleHomRestrict B A g₂ _ sT e₂ y₂ := by
  obtain ⟨J₁, hj₁J₁, hj₂J₁⟩ := directed_of (· ≤ ·) j₁ j₂
  have hiJ₁ : i ≤ J₁ := h₁.trans hj₁J₁
  have h₂₁ : pr₂ ≫ W₂.obj.hom = W₁₂.obj.hom := hpb.w.symm.trans h₁₂
  have hZ : pullback.fst W₁₂.obj.hom (coneStageHom B Dg c hX i) ≫ W₁₂.obj.hom =
      pullback.snd W₁₂.obj.hom (coneStageHom B Dg c hX i) ≫ coneStageHom B Dg c hX i :=
    pullback.condition
  -- the maps from the overlap to the two members, at the vertex and at the stage `J₁`
  obtain ⟨β₁, hβ₁f, hβ₁s⟩ : ∃ β : pullback W₁₂.obj.hom (coneStageHom B Dg c hX i) ⟶
      pullback W₁.obj.hom (coneStageHom B Dg c hX i),
      β ≫ pullback.fst W₁.obj.hom (coneStageHom B Dg c hX i) =
        pullback.fst W₁₂.obj.hom (coneStageHom B Dg c hX i) ≫ pr₁ ∧
      β ≫ pullback.snd W₁.obj.hom (coneStageHom B Dg c hX i) =
        pullback.snd W₁₂.obj.hom (coneStageHom B Dg c hX i) :=
    ⟨pullback.lift _ _ (by rw [Category.assoc, h₁₂, hZ]), pullback.lift_fst _ _ _,
      pullback.lift_snd _ _ _⟩
  obtain ⟨β₂, hβ₂f, hβ₂s⟩ : ∃ β : pullback W₁₂.obj.hom (coneStageHom B Dg c hX i) ⟶
      pullback W₂.obj.hom (coneStageHom B Dg c hX i),
      β ≫ pullback.fst W₂.obj.hom (coneStageHom B Dg c hX i) =
        pullback.fst W₁₂.obj.hom (coneStageHom B Dg c hX i) ≫ pr₂ ∧
      β ≫ pullback.snd W₂.obj.hom (coneStageHom B Dg c hX i) =
        pullback.snd W₁₂.obj.hom (coneStageHom B Dg c hX i) :=
    ⟨pullback.lift _ _ (by rw [Category.assoc, h₂₁, hZ]), pullback.lift_fst _ _ _,
      pullback.lift_snd _ _ _⟩
  obtain ⟨γ₁, hγ₁f, hγ₁s⟩ : ∃ γ : pullback W₁₂.obj.hom (systemStageHom B Dg hiJ₁) ⟶
      pullback W₁.obj.hom (systemStageHom B Dg h₁),
      γ ≫ pullback.fst W₁.obj.hom (systemStageHom B Dg h₁) =
        pullback.fst W₁₂.obj.hom (systemStageHom B Dg hiJ₁) ≫ pr₁ ∧
      γ ≫ pullback.snd W₁.obj.hom (systemStageHom B Dg h₁) =
        pullback.snd W₁₂.obj.hom (systemStageHom B Dg hiJ₁) ≫ systemStageHom B Dg hj₁J₁ :=
    ⟨pullback.lift _ _ (by rw [Category.assoc, h₁₂, pullback.condition, Category.assoc,
      systemStageHom_comp]), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  obtain ⟨γ₂, hγ₂f, hγ₂s⟩ : ∃ γ : pullback W₁₂.obj.hom (systemStageHom B Dg hiJ₁) ⟶
      pullback W₂.obj.hom (systemStageHom B Dg h₂),
      γ ≫ pullback.fst W₂.obj.hom (systemStageHom B Dg h₂) =
        pullback.fst W₁₂.obj.hom (systemStageHom B Dg hiJ₁) ≫ pr₂ ∧
      γ ≫ pullback.snd W₂.obj.hom (systemStageHom B Dg h₂) =
        pullback.snd W₁₂.obj.hom (systemStageHom B Dg hiJ₁) ≫ systemStageHom B Dg hj₂J₁ :=
    ⟨pullback.lift _ _ (by rw [Category.assoc, h₂₁, pullback.condition, Category.assoc,
      systemStageHom_comp]), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have eγ₁ : γ₁ ≫ pullback.fst W₁.obj.hom (systemStageHom B Dg h₁) ≫ W₁.obj.hom =
      pullback.fst W₁₂.obj.hom (systemStageHom B Dg hiJ₁) ≫ W₁₂.obj.hom := by
    rw [reassoc_of% hγ₁f, h₁₂]
  have eγ₂ : γ₂ ≫ pullback.fst W₂.obj.hom (systemStageHom B Dg h₂) ≫ W₂.obj.hom =
      pullback.fst W₁₂.obj.hom (systemStageHom B Dg hiJ₁) ≫ W₁₂.obj.hom := by
    rw [reassoc_of% hγ₂f, h₂₁]
  have eβ₁ : β₁ ≫ pullback.fst W₁.obj.hom (coneStageHom B Dg c hX i) ≫ W₁.obj.hom =
      pullback.fst W₁₂.obj.hom (coneStageHom B Dg c hX i) ≫ W₁₂.obj.hom := by
    rw [reassoc_of% hβ₁f, h₁₂]
  have eβ₂ : β₂ ≫ pullback.fst W₂.obj.hom (coneStageHom B Dg c hX i) ≫ W₂.obj.hom =
      pullback.fst W₁₂.obj.hom (coneStageHom B Dg c hX i) ≫ W₁₂.obj.hom := by
    rw [reassoc_of% hβ₂f, h₂₁]
  have hm₁ : memberConeHom B Dg c hX i W₁₂ ⟨J₁, hiJ₁⟩ ≫ γ₁ =
      β₁ ≫ memberConeHom B Dg c hX i W₁ ⟨j₁, h₁⟩ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hγ₁f, memberConeHom_fst_assoc, Category.assoc, memberConeHom_fst, hβ₁f]
    · rw [Category.assoc, hγ₁s, memberConeHom_snd_assoc, Category.assoc, memberConeHom_snd,
        reassoc_of% hβ₁s, coneStageHom_comp]
  have hm₂ : memberConeHom B Dg c hX i W₁₂ ⟨J₁, hiJ₁⟩ ≫ γ₂ =
      β₂ ≫ memberConeHom B Dg c hX i W₂ ⟨j₂, h₂⟩ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hγ₂f, memberConeHom_fst_assoc, Category.assoc, memberConeHom_fst, hβ₂f]
    · rw [Category.assoc, hγ₂s, memberConeHom_snd_assoc, Category.assoc, memberConeHom_snd,
        reassoc_of% hβ₂s, coneStageHom_comp]
  -- the two restrictions agree at the vertex
  have hv₁ := (smallEtaleHomRestrict_restrict B A (f := γ₁) (e := eγ₁)
      (f' := memberConeHom B Dg c hX i W₁₂ ⟨J₁, hiJ₁⟩)
      (e' := memberConeHom_fst_assoc B Dg c hX i W₁₂ ⟨J₁, hiJ₁⟩ W₁₂.obj.hom)
      (f'' := β₁ ≫ memberConeHom B Dg c hX i W₁ ⟨j₁, h₁⟩)
      (e'' := by rw [Category.assoc, memberConeHom_fst_assoc, eβ₁]) (h := hm₁) (x := y₁)).trans
    ((smallEtaleHomRestrict_restrict B A
      (e := memberConeHom_fst_assoc B Dg c hX i W₁ ⟨j₁, h₁⟩ W₁.obj.hom) (f' := β₁) (e' := eβ₁)
      (e'' := by rw [Category.assoc, memberConeHom_fst_assoc, eβ₁]) (h := rfl) (x := y₁)).symm.trans
    ((congrArg (smallEtaleHomRestrict B A β₁ _ _ eβ₁) hy₁).trans
      (smallEtaleHomRestrict_restrict B A (e := pullback.condition.symm) (f' := β₁) (e' := eβ₁)
        (f'' := pullback.snd W₁₂.obj.hom (coneStageHom B Dg c hX i)) (e'' := hZ.symm)
        (h := hβ₁s) (x := a))))
  have hv₂ := (smallEtaleHomRestrict_restrict B A (f := γ₂) (e := eγ₂)
      (f' := memberConeHom B Dg c hX i W₁₂ ⟨J₁, hiJ₁⟩)
      (e' := memberConeHom_fst_assoc B Dg c hX i W₁₂ ⟨J₁, hiJ₁⟩ W₁₂.obj.hom)
      (f'' := β₂ ≫ memberConeHom B Dg c hX i W₂ ⟨j₂, h₂⟩)
      (e'' := by rw [Category.assoc, memberConeHom_fst_assoc, eβ₂]) (h := hm₂) (x := y₂)).trans
    ((smallEtaleHomRestrict_restrict B A
      (e := memberConeHom_fst_assoc B Dg c hX i W₂ ⟨j₂, h₂⟩ W₂.obj.hom) (f' := β₂) (e' := eβ₂)
      (e'' := by rw [Category.assoc, memberConeHom_fst_assoc, eβ₂]) (h := rfl) (x := y₂)).symm.trans
    ((congrArg (smallEtaleHomRestrict B A β₂ _ _ eβ₂) hy₂).trans
      (smallEtaleHomRestrict_restrict B A (e := pullback.condition.symm) (f' := β₂) (e' := eβ₂)
        (f'' := pullback.snd W₁₂.obj.hom (coneStageHom B Dg c hX i)) (e'' := hZ.symm)
        (h := hβ₂s) (x := a))))
  -- injectivity over the member system of the overlap
  have eu₁ : (pullback.fst W₁₂.obj.hom (systemStageHom B Dg hiJ₁) ≫ pr₁) ≫ W₁.obj.hom =
      pullback.fst W₁₂.obj.hom (systemStageHom B Dg hiJ₁) ≫ W₁₂.obj.hom := by
    rw [Category.assoc, h₁₂]
  have eu₂ : (pullback.fst W₁₂.obj.hom (systemStageHom B Dg hiJ₁) ≫ pr₂) ≫ W₂.obj.hom =
      pullback.fst W₁₂.obj.hom (systemStageHom B Dg hiJ₁) ≫ W₁₂.obj.hom := by
    rw [Category.assoc, h₂₁]
  have hvert := fun x => (smallEtaleTrivAlong_restrict B A φ₁ ψ₂ _ _ _ eu₁ eu₂
    (memberConeHom B Dg c hX i W₁₂ ⟨J₁, hiJ₁⟩)
    (pullback.fst W₁₂.obj.hom (coneStageHom B Dg c hX i) ≫ pr₁)
    (pullback.fst W₁₂.obj.hom (coneStageHom B Dg c hX i) ≫ pr₂)
    (pullback.fst W₁₂.obj.hom (coneStageHom B Dg c hX i) ≫ W₁₂.obj.hom)
    (by rw [Category.assoc, h₁₂]) (by rw [Category.assoc, h₂₁])
    (memberConeHom_fst_assoc B Dg c hX i W₁₂ ⟨J₁, hiJ₁⟩ pr₁)
    (memberConeHom_fst_assoc B Dg c hX i W₁₂ ⟨J₁, hiJ₁⟩ pr₂)
    (memberConeHom_fst_assoc B Dg c hX i W₁₂ ⟨J₁, hiJ₁⟩ W₁₂.obj.hom) x).symm
  obtain ⟨J₂, hJ₂, hJ₂'⟩ := exists_stage_transport_eq_of_transport_eq B
    (memberSystem B Dg i W₁₂) (memberCone B Dg c hX i W₁₂) (memberCone_contains B Dg c hX i W₁₂)
    (memberConeIsLimit B Dg c hX i W₁₂ hc) (memberSystem_isAffineHom haff)
    (memberSystem_compactSpace haff hWc) (memberSystem_quasiSeparatedSpace haff hWq) P hloc hinj
    ⟨J₁, hiJ₁⟩ hE
    ((smallEtaleTrivAlong B A φ₁ _ _ eu₁).inv ≫
      smallEtaleHomRestrict B A γ₁ _ _ eγ₁ y₁ ≫ (smallEtaleTrivAlong B A ψ₂ _ _ eu₂).hom)
    ((smallEtaleTrivAlong B A φ₁ _ _ eu₁).inv ≫
      smallEtaleHomRestrict B A γ₂ _ _ eγ₂ y₂ ≫ (smallEtaleTrivAlong B A ψ₂ _ _ eu₂).hom)
    ((hvert _).trans ((congrArg (fun z => _ ≫ z ≫ _) (hv₁.trans hv₂.symm)).trans
      (hvert _).symm))
  -- read back at the stage `J₂`
  have hnJ : memberSystemHom B Dg i W₁₂ hJ₂ ≫
      pullback.fst W₁₂.obj.hom (systemStageHom B Dg hiJ₁) ≫ W₁₂.obj.hom =
      pullback.fst W₁₂.obj.hom (systemStageHom B Dg J₂.2) ≫ W₁₂.obj.hom :=
    memberSystemHom_fst_assoc B Dg i W₁₂ hJ₂ W₁₂.obj.hom
  have hr := fun x => smallEtaleTrivAlong_restrict B A φ₁ ψ₂ _ _ _ eu₁ eu₂
    (memberSystemHom B Dg i W₁₂ hJ₂)
    (pullback.fst W₁₂.obj.hom (systemStageHom B Dg J₂.2) ≫ pr₁)
    (pullback.fst W₁₂.obj.hom (systemStageHom B Dg J₂.2) ≫ pr₂)
    (pullback.fst W₁₂.obj.hom (systemStageHom B Dg J₂.2) ≫ W₁₂.obj.hom)
    (by rw [Category.assoc, h₁₂]) (by rw [Category.assoc, h₂₁])
    (memberSystemHom_fst_assoc B Dg i W₁₂ hJ₂ pr₁)
    (memberSystemHom_fst_assoc B Dg i W₁₂ hJ₂ pr₂) hnJ x
  have hn : smallEtaleHomRestrict B A (memberSystemHom B Dg i W₁₂ hJ₂) _ _ hnJ
        (smallEtaleHomRestrict B A γ₁ _ _ eγ₁ y₁) =
      smallEtaleHomRestrict B A (memberSystemHom B Dg i W₁₂ hJ₂) _ _ hnJ
        (smallEtaleHomRestrict B A γ₂ _ _ eγ₂ y₂) := by
    have h := (hr _).trans (hJ₂'.trans (hr _).symm)
    rw [← cancel_epi (smallEtaleTrivAlong B A φ₁ _ _ (by rw [Category.assoc, h₁₂])).inv,
      ← cancel_mono (smallEtaleTrivAlong B A ψ₂ _ _ (by rw [Category.assoc, h₂₁])).hom]
    simpa only [Category.assoc] using h
  refine ⟨J₂.1, hj₁J₁.trans hJ₂, hj₂J₁.trans hJ₂, fun J hJ T g₁ g₂ v hg₁ hg₂ sT e₁ e₂ => ?_⟩
  -- a scheme mapping to both maps to the overlap at the stage `J₂`
  have hcomm : (g₁ ≫ pullback.fst W₁.obj.hom (systemStageHom B Dg h₁)) ≫ W₁.obj.hom =
      (g₂ ≫ pullback.fst W₂.obj.hom (systemStageHom B Dg h₂)) ≫ W₂.obj.hom := by
    rw [Category.assoc, Category.assoc, pullback.condition, pullback.condition, reassoc_of% hg₁,
      reassoc_of% hg₂, systemStageHom_comp, systemStageHom_comp]
  obtain ⟨m, hmf, hms⟩ : ∃ m : T ⟶ pullback W₁₂.obj.hom (systemStageHom B Dg J₂.2),
      m ≫ pullback.fst W₁₂.obj.hom (systemStageHom B Dg J₂.2) = hpb.lift _ _ hcomm ∧
      m ≫ pullback.snd W₁₂.obj.hom (systemStageHom B Dg J₂.2) = v ≫ systemStageHom B Dg hJ :=
    ⟨pullback.lift _ _ (by rw [← h₁₂, hpb.lift_fst_assoc, Category.assoc, pullback.condition,
      reassoc_of% hg₁, Category.assoc, systemStageHom_comp, systemStageHom_comp]),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hg₁' : m ≫ memberSystemHom B Dg i W₁₂ hJ₂ ≫ γ₁ = g₁ := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, hγ₁f, memberSystemHom_fst_assoc, reassoc_of% hmf,
        hpb.lift_fst]
    · rw [Category.assoc, Category.assoc, hγ₁s, memberSystemHom_snd_assoc, reassoc_of% hms,
        systemStageHom_comp, systemStageHom_comp, hg₁]
  have hg₂' : m ≫ memberSystemHom B Dg i W₁₂ hJ₂ ≫ γ₂ = g₂ := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, hγ₂f, memberSystemHom_fst_assoc, reassoc_of% hmf,
        hpb.lift_snd]
    · rw [Category.assoc, Category.assoc, hγ₂s, memberSystemHom_snd_assoc, reassoc_of% hms,
        systemStageHom_comp, systemStageHom_comp, hg₂]
  have hs : m ≫ pullback.fst W₁₂.obj.hom (systemStageHom B Dg J₂.2) ≫ W₁₂.obj.hom = sT := by
    rw [← e₁, ← hg₁', Category.assoc, Category.assoc, eγ₁, hnJ]
  have k₁ := (smallEtaleHomRestrict_restrict B A (f := γ₁) (e := eγ₁)
      (f' := memberSystemHom B Dg i W₁₂ hJ₂) (e' := hnJ)
      (f'' := memberSystemHom B Dg i W₁₂ hJ₂ ≫ γ₁)
      (e'' := by rw [Category.assoc, eγ₁, hnJ]) (h := rfl) (x := y₁))
  have k₂ := (smallEtaleHomRestrict_restrict B A (f := γ₂) (e := eγ₂)
      (f' := memberSystemHom B Dg i W₁₂ hJ₂) (e' := hnJ)
      (f'' := memberSystemHom B Dg i W₁₂ hJ₂ ≫ γ₂)
      (e'' := by rw [Category.assoc, eγ₂, hnJ]) (h := rfl) (x := y₂))
  have l₁ := smallEtaleHomRestrict_restrict B A (f := memberSystemHom B Dg i W₁₂ hJ₂ ≫ γ₁)
      (e := by rw [Category.assoc, eγ₁, hnJ]) (f' := m) (e' := hs) (f'' := g₁)
      (e'' := e₁) (h := hg₁') (x := y₁)
  have l₂ := smallEtaleHomRestrict_restrict B A (f := memberSystemHom B Dg i W₁₂ hJ₂ ≫ γ₂)
      (e := by rw [Category.assoc, eγ₂, hnJ]) (f' := m) (e' := hs) (f'' := g₂)
      (e'' := e₂) (h := hg₂') (x := y₂)
  rw [← l₁, ← l₂, ← k₁, ← k₂, hn]

/-- The overlap of two members of a family of morphisms to `S`, their fibre product, named for
the gluing along a covering. -/
public abbrev smallEtaleFullnessOverlap {S : B.Scheme} {K : Type*} {X : K → B.Scheme}
    (f : ∀ k, X k ⟶ S) (k l : K) : B.Scheme :=
  pullback (f k) (f l)

/-- The first projection of the overlap of two members. -/
public abbrev smallEtaleFullnessOverlapFst {S : B.Scheme} {K : Type*} {X : K → B.Scheme}
    (f : ∀ k, X k ⟶ S) (k l : K) : smallEtaleFullnessOverlap B f k l ⟶ X k :=
  pullback.fst (f k) (f l)

/-- The second projection of the overlap of two members. -/
public abbrev smallEtaleFullnessOverlapSnd {S : B.Scheme} {K : Type*} {X : K → B.Scheme}
    (f : ∀ k, X k ⟶ S) (k l : K) : smallEtaleFullnessOverlap B f k l ⟶ X l :=
  pullback.snd (f k) (f l)

/-- The structure morphism of the overlap of two members. -/
public abbrev smallEtaleFullnessOverlapHom {S : B.Scheme} {K : Type*} {X : K → B.Scheme}
    (f : ∀ k, X k ⟶ S) (k l : K) : smallEtaleFullnessOverlap B f k l ⟶ S :=
  pullback.fst (f k) (f l) ≫ f k

/-- The overlap of two members is their fibre product. -/
public theorem isPullback_smallEtaleFullnessOverlap {S : B.Scheme} {K : Type*}
    {X : K → B.Scheme} (f : ∀ k, X k ⟶ S) (k l : K) :
    IsPullback (smallEtaleFullnessOverlapFst B f k l) (smallEtaleFullnessOverlapSnd B f k l)
      (f k) (f l) :=
  IsPullback.of_hasPullback _ _

/-- **Faithfulness for sheaves trivialized on a finite affine covering.** -/
public theorem exists_stage_map_eq_of_trivializations (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (P : A → Prop) (hloc : SmallEtaleConstantMapsLocallyConstant B A P)
    (hinj : SmallEtaleConstantFaithful B A) (i : I) {K : Type (u + 1)} [Finite K]
    (W : K → SmallEtale B (Dg.obj (op i)).obj (Dg.obj (op i)).property)
    (hW : Sieve.ofArrows W (fun k => (SmallEtale.finalIsTerminal B (Dg.obj (op i)).obj
        (Dg.obj (op i)).property).from (W k)) ∈ SmallEtale.topology B (Dg.obj (op i)).obj
        (Dg.obj (op i)).property (SmallEtale.final B (Dg.obj (op i)).obj
          (Dg.obj (op i)).property))
    (hWaff : ∀ k, IsAffine (W k).obj.left.obj)
    {F G : Sheaf (SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property) A}
    (E E' : K → A) (hE : ∀ k, P (E k))
    (φ : ∀ k, (smallEtaleSheafPullback B A (W k).obj.hom).obj F ≅
      (constantSheaf (SmallEtale.topology B (W k).obj.left.obj (W k).obj.left.property) A).obj
        (E k))
    (ψ : ∀ k, (smallEtaleSheafPullback B A (W k).obj.hom).obj G ≅
      (constantSheaf (SmallEtale.topology B (W k).obj.left.obj (W k).obj.left.property) A).obj
        (E' k))
    (a b : F ⟶ G)
    (hab : (smallEtaleSheafPullback B A (coneStageHom B Dg c hX i)).map a =
      (smallEtaleSheafPullback B A (coneStageHom B Dg c hX i)).map b) :
    ∃ j, ∃ h : i ≤ j, (smallEtaleSheafPullback B A (systemStageHom B Dg h)).map a =
      (smallEtaleSheafPullback B A (systemStageHom B Dg h)).map b := by
  choose j hij hj using fun k =>
    have := hWaff k
    exists_stage_map_eq_member B Dg c hX hc haff P hloc hinj i (W k) (hE k) (φ k) (ψ k) a b hab
  have : Nonempty I := ⟨i⟩
  obtain ⟨J, hJ⟩ := Finite.exists_le (fun o : Option K => o.elim i j)
  have hiJ : i ≤ J := hJ none
  let V := fun k => (smallEtaleBaseChange B (systemStageHom B Dg hiJ)).obj (W k)
  exact ⟨J, hiJ, eq_of_smallEtaleHomRestrict_pullback_snd_eq B _ _ W hW _ _ fun k =>
    (smallEtaleHomRestrict_map B A _ _ _ _ a).trans ((hj k J hiJ (hJ (some k))).trans
      (smallEtaleHomRestrict_map B A _ _ _ _ b).symm)⟩

omit [∀ (S : B.Scheme), HasWeakSheafify (SmallEtale.topology B S.obj S.property) A]
  [IsDirected I (· ≤ ·)] in
/-- **Two restrictions agree over an overlap at a late stage**, the form of
`AlgebraicGeometry.exists_stage_restrict_eq_overlap` used in the gluing. -/
public theorem smallEtaleHomRestrict_memberSystemHom_overlap {i J : I} (hiJ : i ≤ J)
    (W₁ W₂ : SmallEtale B (Dg.obj (op i)).obj (Dg.obj (op i)).property)
    {F G : Sheaf (SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property) A}
    {j₁ j₂ : I} (h₁ : i ≤ j₁) (h₂ : i ≤ j₂) (hj₁ : j₁ ≤ J) (hj₂ : j₂ ≤ J)
    (y₁ : (smallEtaleSheafPullback B A
        (pullback.fst W₁.obj.hom (systemStageHom B Dg h₁) ≫ W₁.obj.hom)).obj F ⟶
      (smallEtaleSheafPullback B A
        (pullback.fst W₁.obj.hom (systemStageHom B Dg h₁) ≫ W₁.obj.hom)).obj G)
    (y₂ : (smallEtaleSheafPullback B A
        (pullback.fst W₂.obj.hom (systemStageHom B Dg h₂) ≫ W₂.obj.hom)).obj F ⟶
      (smallEtaleSheafPullback B A
        (pullback.fst W₂.obj.hom (systemStageHom B Dg h₂) ≫ W₂.obj.hom)).obj G)
    (H : ∀ {T : B.Scheme}
      (g₁ : T ⟶ pullback W₁.obj.hom (systemStageHom B Dg h₁))
      (g₂ : T ⟶ pullback W₂.obj.hom (systemStageHom B Dg h₂)) (v : T ⟶ Dg.obj (op J))
      (_ : g₁ ≫ pullback.snd _ _ = v ≫ systemStageHom B Dg hj₁)
      (_ : g₂ ≫ pullback.snd _ _ = v ≫ systemStageHom B Dg hj₂)
      (sT : T ⟶ Dg.obj (op i))
      (e₁ : g₁ ≫ pullback.fst W₁.obj.hom (systemStageHom B Dg h₁) ≫ W₁.obj.hom = sT)
      (e₂ : g₂ ≫ pullback.fst W₂.obj.hom (systemStageHom B Dg h₂) ≫ W₂.obj.hom = sT),
      smallEtaleHomRestrict B A g₁ _ sT e₁ y₁ = smallEtaleHomRestrict B A g₂ _ sT e₂ y₂)
    {O : B.Scheme} (p : O ⟶ pullback W₁.obj.hom (systemStageHom B Dg hiJ))
    (q : O ⟶ pullback W₂.obj.hom (systemStageHom B Dg hiJ))
    (hpq : p ≫ pullback.snd _ _ = q ≫ pullback.snd _ _) (s₀ : O ⟶ Dg.obj (op i))
    (e₁ : p ≫ pullback.fst W₁.obj.hom (systemStageHom B Dg hiJ) ≫ W₁.obj.hom = s₀)
    (e₂ : q ≫ pullback.fst W₂.obj.hom (systemStageHom B Dg hiJ) ≫ W₂.obj.hom = s₀) :
    smallEtaleHomRestrict B A p _ s₀ e₁ (smallEtaleHomRestrict B A
        (memberSystemHom B Dg i W₁ (show (⟨j₁, h₁⟩ : {j : I // i ≤ j}) ≤ ⟨J, hiJ⟩ from hj₁)) _ _
        (memberSystemHom_fst_assoc B Dg i W₁ _ W₁.obj.hom) y₁) =
      smallEtaleHomRestrict B A q _ s₀ e₂ (smallEtaleHomRestrict B A
        (memberSystemHom B Dg i W₂ (show (⟨j₂, h₂⟩ : {j : I // i ≤ j}) ≤ ⟨J, hiJ⟩ from hj₂)) _ _
        (memberSystemHom_fst_assoc B Dg i W₂ _ W₂.obj.hom) y₂) := by
  have k₁ := smallEtaleHomRestrict_restrict B A
    (f := memberSystemHom B Dg i W₁ (show (⟨j₁, h₁⟩ : {j : I // i ≤ j}) ≤ ⟨J, hiJ⟩ from hj₁))
    (e := memberSystemHom_fst_assoc B Dg i W₁ _ W₁.obj.hom) (f' := p) (e' := e₁)
    (e'' := (Category.assoc _ _ _).trans ((congrArg (p ≫ ·)
      (memberSystemHom_fst_assoc B Dg i W₁ _ W₁.obj.hom)).trans e₁)) (h := rfl) (x := y₁)
  have k₂ := smallEtaleHomRestrict_restrict B A
    (f := memberSystemHom B Dg i W₂ (show (⟨j₂, h₂⟩ : {j : I // i ≤ j}) ≤ ⟨J, hiJ⟩ from hj₂))
    (e := memberSystemHom_fst_assoc B Dg i W₂ _ W₂.obj.hom) (f' := q) (e' := e₂)
    (e'' := (Category.assoc _ _ _).trans ((congrArg (q ≫ ·)
      (memberSystemHom_fst_assoc B Dg i W₂ _ W₂.obj.hom)).trans e₂)) (h := rfl) (x := y₂)
  refine k₁.trans (Eq.trans ?_ k₂.symm)
  refine H _ _ (p ≫ pullback.snd _ _) ?_ ?_ s₀ _ _
  · rw [Category.assoc, memberSystemHom_snd, Category.assoc]
  · rw [Category.assoc, memberSystemHom_snd, hpq, Category.assoc]

omit [∀ (S : B.Scheme), HasWeakSheafify (SmallEtale.topology B S.obj S.property) A]
  [IsDirected I (· ≤ ·)] in
/-- **The glued morphism has the right restriction over a member at the vertex.** -/
public theorem smallEtaleHomRestrict_coneStageHom_member {i J : I} (hiJ : i ≤ J)
    (W : SmallEtale B (Dg.obj (op i)).obj (Dg.obj (op i)).property)
    {F G : Sheaf (SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property) A}
    {j : I} (h : i ≤ j) (hjJ : j ≤ J)
    (y : (smallEtaleSheafPullback B A
        (pullback.fst W.obj.hom (systemStageHom B Dg h) ≫ W.obj.hom)).obj F ⟶
      (smallEtaleSheafPullback B A
        (pullback.fst W.obj.hom (systemStageHom B Dg h) ≫ W.obj.hom)).obj G)
    (a : (smallEtaleSheafPullback B A (coneStageHom B Dg c hX i)).obj F ⟶
      (smallEtaleSheafPullback B A (coneStageHom B Dg c hX i)).obj G)
    (hy : smallEtaleHomRestrict B A (memberConeHom B Dg c hX i W ⟨j, h⟩)
        (pullback.fst W.obj.hom (systemStageHom B Dg h) ≫ W.obj.hom)
        (pullback.fst W.obj.hom (coneStageHom B Dg c hX i) ≫ W.obj.hom)
        (memberConeHom_fst_assoc B Dg c hX i W ⟨j, h⟩ W.obj.hom) y =
      smallEtaleHomRestrict B A (pullback.snd W.obj.hom (coneStageHom B Dg c hX i))
        (coneStageHom B Dg c hX i)
        (pullback.fst W.obj.hom (coneStageHom B Dg c hX i) ≫ W.obj.hom)
        pullback.condition.symm a)
    (b : (smallEtaleSheafPullback B A (systemStageHom B Dg hiJ)).obj F ⟶
      (smallEtaleSheafPullback B A (systemStageHom B Dg hiJ)).obj G)
    (hb : smallEtaleHomRestrict B A (pullback.snd W.obj.hom (systemStageHom B Dg hiJ))
        (systemStageHom B Dg hiJ) (pullback.fst W.obj.hom (systemStageHom B Dg hiJ) ≫ W.obj.hom)
        pullback.condition.symm b =
      smallEtaleHomRestrict B A
        (memberSystemHom B Dg i W (show (⟨j, h⟩ : {j : I // i ≤ j}) ≤ ⟨J, hiJ⟩ from hjJ)) _ _
        (memberSystemHom_fst_assoc B Dg i W _ W.obj.hom) y) :
    smallEtaleHomRestrict B A (pullback.snd W.obj.hom (coneStageHom B Dg c hX i))
        (coneStageHom B Dg c hX i)
        (pullback.fst W.obj.hom (coneStageHom B Dg c hX i) ≫ W.obj.hom) pullback.condition.symm
        (smallEtaleHomRestrict B A (coneStageHom B Dg c hX J) (systemStageHom B Dg hiJ)
          (coneStageHom B Dg c hX i) (coneStageHom_comp B Dg c hX hiJ) b) =
      smallEtaleHomRestrict B A (pullback.snd W.obj.hom (coneStageHom B Dg c hX i))
        (coneStageHom B Dg c hX i)
        (pullback.fst W.obj.hom (coneStageHom B Dg c hX i) ≫ W.obj.hom)
        pullback.condition.symm a := by
  have e₀ : (memberConeHom B Dg c hX i W ⟨J, hiJ⟩ ≫
      pullback.snd W.obj.hom (systemStageHom B Dg hiJ)) ≫ systemStageHom B Dg hiJ =
      pullback.fst W.obj.hom (coneStageHom B Dg c hX i) ≫ W.obj.hom := by
    rw [Category.assoc, ← pullback.condition, memberConeHom_fst_assoc]
  exact (smallEtaleHomRestrict_restrict B A (e := coneStageHom_comp B Dg c hX hiJ)
      (f' := pullback.snd W.obj.hom (coneStageHom B Dg c hX i))
      (e' := pullback.condition.symm)
      (f'' := memberConeHom B Dg c hX i W ⟨J, hiJ⟩ ≫
        pullback.snd W.obj.hom (systemStageHom B Dg hiJ))
      (e'' := e₀) (h := (memberConeHom_snd B Dg c hX i W ⟨J, hiJ⟩).symm) (x := b)).trans
    ((smallEtaleHomRestrict_restrict B A (f := pullback.snd W.obj.hom (systemStageHom B Dg hiJ))
      (e := pullback.condition.symm) (f' := memberConeHom B Dg c hX i W ⟨J, hiJ⟩)
      (e' := memberConeHom_fst_assoc B Dg c hX i W ⟨J, hiJ⟩ W.obj.hom)
      (e'' := e₀) (h := rfl) (x := b)).symm.trans
    ((congrArg (smallEtaleHomRestrict B A (memberConeHom B Dg c hX i W ⟨J, hiJ⟩) _ _
      (memberConeHom_fst_assoc B Dg c hX i W ⟨J, hiJ⟩ W.obj.hom)) hb).trans
    ((smallEtaleHomRestrict_restrict B A
      (f := memberSystemHom B Dg i W (show (⟨j, h⟩ : {j : I // i ≤ j}) ≤ ⟨J, hiJ⟩ from hjJ))
      (e := memberSystemHom_fst_assoc B Dg i W _ W.obj.hom)
      (f' := memberConeHom B Dg c hX i W ⟨J, hiJ⟩)
      (e' := memberConeHom_fst_assoc B Dg c hX i W ⟨J, hiJ⟩ W.obj.hom)
      (f'' := memberConeHom B Dg c hX i W ⟨j, h⟩)
      (e'' := memberConeHom_fst_assoc B Dg c hX i W _ W.obj.hom)
      (h := memberConeHom_comp_memberSystemHom B Dg c hX i W _) (x := y)).trans hy)))

/-- **Fullness for sheaves trivialized on a finite affine covering.** -/
public theorem exists_stage_restrict_eq_of_trivializations (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj)
    (P : A → Prop) (hloc : SmallEtaleConstantMapsLocallyConstant B A P)
    (hinj : SmallEtaleConstantFaithful B A) (i : I) {K : Type (u + 1)} [Finite K]
    (W : K → SmallEtale B (Dg.obj (op i)).obj (Dg.obj (op i)).property)
    (hW : Sieve.ofArrows W (fun k => (SmallEtale.finalIsTerminal B (Dg.obj (op i)).obj
        (Dg.obj (op i)).property).from (W k)) ∈ SmallEtale.topology B (Dg.obj (op i)).obj
        (Dg.obj (op i)).property (SmallEtale.final B (Dg.obj (op i)).obj
          (Dg.obj (op i)).property))
    (hWaff : ∀ k, IsAffine (W k).obj.left.obj)
    {F G : Sheaf (SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property) A}
    (E E' : K → A) (hE : ∀ k, P (E k))
    (φ : ∀ k, (smallEtaleSheafPullback B A (W k).obj.hom).obj F ≅
      (constantSheaf (SmallEtale.topology B (W k).obj.left.obj (W k).obj.left.property) A).obj
        (E k))
    (ψ : ∀ k, (smallEtaleSheafPullback B A (W k).obj.hom).obj G ≅
      (constantSheaf (SmallEtale.topology B (W k).obj.left.obj (W k).obj.left.property) A).obj
        (E' k))
    (a : (smallEtaleSheafPullback B A (coneStageHom B Dg c hX i)).obj F ⟶
      (smallEtaleSheafPullback B A (coneStageHom B Dg c hX i)).obj G) :
    ∃ j, ∃ h : i ≤ j, ∃ b : (smallEtaleSheafPullback B A (systemStageHom B Dg h)).obj F ⟶
        (smallEtaleSheafPullback B A (systemStageHom B Dg h)).obj G,
      smallEtaleHomRestrict B A (coneStageHom B Dg c hX j) (systemStageHom B Dg h)
        (coneStageHom B Dg c hX i) (coneStageHom_comp B Dg c hX h) b = a := by
  have := hqs i
  -- local solutions over the members
  choose j hij y hy using fun k =>
    have := hWaff k
    exists_stage_restrict_eq_member B Dg c hX hc haff P hloc hinj i (W k) (hE k) (φ k) (ψ k) a
  -- their agreement over the overlaps at late stages
  choose J₀ hJ₁ hJ₂ hJ using fun p : K × K =>
    have := hWaff p.1
    have := hWaff p.2
    exists_stage_restrict_eq_overlap B Dg c hX hc haff P hloc hinj i (W p.1) (W p.2)
      (smallEtaleMemberOverlap B (W p.1) (W p.2)) (pullback.fst _ _) (pullback.snd _ _)
      (IsPullback.of_hasPullback _ _) rfl
      (hWc := (compactSpace_quasiSeparatedSpace_bigEtalePullback B (W p.1).obj.hom
        (W p.2).obj.hom).1)
      (hWq := (compactSpace_quasiSeparatedSpace_bigEtalePullback B (W p.1).obj.hom
        (W p.2).obj.hom).2)
      (hE p.1) (φ p.1) (ψ p.2) a (hij p.1) (hij p.2) (y p.1) (y p.2) (hy p.1) (hy p.2)
  have : Nonempty I := ⟨i⟩
  obtain ⟨J, hJle⟩ := Finite.exists_le
    (fun o : Option (K ⊕ (K × K)) => o.elim i (Sum.elim j J₀))
  have hiJ : i ≤ J := hJle none
  have hjJ : ∀ k, j k ≤ J := fun k => hJle (some (Sum.inl k))
  have hJ₀J : ∀ p, J₀ p ≤ J := fun p => hJle (some (Sum.inr p))
  let t := systemStageHom B Dg hiJ
  let V := fun k => (smallEtaleBaseChange B t).obj (W k)
  let δ := fun k => memberSystemHom B Dg i (W k)
    (show (⟨j k, hij k⟩ : {j : I // i ≤ j}) ≤ ⟨J, hiJ⟩ from hjJ k)
  -- glue the local solutions at the stage `J`
  let f := SmallEtaleGluing.memberHom B _ V
  obtain ⟨b, hb⟩ := smallEtaleHomRestrict_glue B A t f
    (SmallEtaleGluing.sieve_ofEtaleHom_memberHom B _ V
      (smallEtale_sieve_ofArrows_final_baseChange B t W _ hW))
    (smallEtaleFullnessOverlap B f) (smallEtaleFullnessOverlapFst B f)
    (smallEtaleFullnessOverlapSnd B f) (smallEtaleFullnessOverlapHom B f)
    (isPullback_smallEtaleFullnessOverlap B f) (fun k l => rfl)
    (fun k l => (isPullback_smallEtaleFullnessOverlap B f k l).w.symm)
    (fun k => pullback.fst (W k).obj.hom t ≫ (W k).obj.hom) (fun k => pullback.condition.symm)
    (fun k => smallEtaleHomRestrict B A (δ k) _ _
      (memberSystemHom_fst_assoc B Dg i (W k) _ (W k).obj.hom) (y k))
    (fun k l e₁ e₂ => smallEtaleHomRestrict_memberSystemHom_overlap B Dg hiJ (W k) (W l)
      (hij k) (hij l) (hjJ k) (hjJ l) (y k) (y l) (hJ (k, l) J (hJ₀J (k, l)))
      (smallEtaleFullnessOverlapFst B f k l) (smallEtaleFullnessOverlapSnd B f k l)
      (isPullback_smallEtaleFullnessOverlap B f k l).w _ e₁ e₂)
  refine ⟨J, hiJ, b, ?_⟩
  -- the glued morphism has the right restriction to the vertex
  exact eq_of_smallEtaleHomRestrict_pullback_snd_eq B _ _ W hW _ _ fun k =>
    smallEtaleHomRestrict_coneStageHom_member B Dg c hX hiJ (W k) (hij k) (hjJ k) (y k) a
      (hy k) b (hb k)

end Members

section General

variable (B : BigEtaleSite.{u}) {A : Type t} [Category.{v} A]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous A
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (X : B.Scheme) (V : SmallEtale B X.obj X.property),
    HasWeakSheafify ((SmallEtale.topology B X.obj X.property).over V) A]
  {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (Dg : Iᵒᵖ ⥤ B.Scheme) (c : Cone (Dg ⋙ B.inclusion)) (hX : B.Contains c.pt)

/-- **Faithfulness of the comparison for trivialized sheaves.** For a directed inverse system of
quasi-compact, quasi-separated schemes with affine transition morphisms and a limit cone, and a
coefficient category in which morphisms of constant sheaves with source satisfying `P` are locally
constant and the constant sheaf functor is faithful over nonempty schemes, the comparison is
faithful on every class `Q` of sheaves trivialized with values satisfying `P`. -/
public theorem smallEtaleStagesFaithful_of_isTrivialized (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj)
    (hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj)
    (P : A → Prop) (hloc : SmallEtaleConstantMapsLocallyConstant B A P)
    (hinj : SmallEtaleConstantFaithful B A) (Q : SmallEtaleSheafProperty B A)
    (hQ : ∀ (X : B.Scheme) (F : Sheaf (SmallEtale.topology B X.obj X.property) A),
      Q X F → IsTrivializedSmallEtaleSheaf B A P X F) :
    SmallEtaleStagesFaithful B A Dg c hX Q := by
  intro i F G hF hG a b hab
  have := hqc i
  have := hqs i
  obtain ⟨K, hK, W, hW, hWaff, hWt⟩ :=
    exists_finite_affine_trivializing B A P _ F G (hQ _ F hF) (hQ _ G hG)
  choose E hE hφ using fun k => (hWt k).1
  choose E' _ hψ using fun k => (hWt k).2
  exact exists_stage_map_eq_of_trivializations B Dg c hX hc haff P hloc hinj i W hW hWaff E E' hE
    (fun k => (hφ k).some) (fun k => (hψ k).some) a b hab

/-- **Fullness of the comparison for trivialized sheaves**, under the hypotheses of
`AlgebraicGeometry.smallEtaleStagesFaithful_of_isTrivialized`. -/
public theorem smallEtaleStagesFull_of_isTrivialized (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj)
    (hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj)
    (P : A → Prop) (hloc : SmallEtaleConstantMapsLocallyConstant B A P)
    (hinj : SmallEtaleConstantFaithful B A) (Q : SmallEtaleSheafProperty B A)
    (hQ : ∀ (X : B.Scheme) (F : Sheaf (SmallEtale.topology B X.obj X.property) A),
      Q X F → IsTrivializedSmallEtaleSheaf B A P X F) :
    SmallEtaleStagesFull B A Dg c hX Q := by
  intro i F G hF hG a
  have := hqc i
  have := hqs i
  obtain ⟨K, hK, W, hW, hWaff, hWt⟩ :=
    exists_finite_affine_trivializing B A P _ F G (hQ _ F hF) (hQ _ G hG)
  choose E hE hφ using fun k => (hWt k).1
  choose E' _ hψ using fun k => (hWt k).2
  obtain ⟨j, h, b, hb⟩ := exists_stage_restrict_eq_of_trivializations B Dg c hX hc haff hqs P
    hloc hinj i W hW hWaff E E' hE (fun k => (hφ k).some) (fun k => (hψ k).some) a
  refine ⟨j, h, b, ?_⟩
  rw [smallEtaleStageComparison_eq, smallEtaleStageComparison_eq]
  exact hb

end General

section Concrete

attribute [local instance] SmallEtale.isRightAdjointPushforward_type
  SmallEtale.isRightAdjointPushforward_addCommGrpCat
  SmallEtale.isRightAdjointPushforward_moduleCat_site

variable (B : BigEtaleSite.{u}) {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (Dg : Iᵒᵖ ⥤ B.Scheme) (c : Cone (Dg ⋙ B.inclusion)) (hX : B.Contains c.pt)

/-- **Tag 0GL2 (1), faithfulness.** Two maps between finite locally constant sheaves of sets at
a stage which agree after inverse image to the limit agree at a later stage. -/
public theorem smallEtaleStagesFaithful_isFiniteLocallyConstant_type (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj)
    (hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj) :
    SmallEtaleStagesFaithful B (Type (u + 1)) Dg c hX
      (isFiniteLocallyConstantSmallEtaleSheaf B (Type (u + 1))) :=
  smallEtaleStagesFaithful_of_isTrivialized B Dg c hX hc haff hqc hqs _
    (smallEtaleConstantMapsLocallyConstant_type B) (smallEtaleConstantFaithful_type B) _
    fun X F hF => (isTrivialized_iff_isFiniteLocallyConstant B (Type (u + 1)) X F).mpr hF

/-- **Tag 0GL2 (1), fullness.** Every map between the inverse images to the limit of two finite
locally constant sheaves of sets at a stage comes from a map at a later stage. -/
public theorem smallEtaleStagesFull_isFiniteLocallyConstant_type (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj)
    (hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj) :
    SmallEtaleStagesFull B (Type (u + 1)) Dg c hX
      (isFiniteLocallyConstantSmallEtaleSheaf B (Type (u + 1))) :=
  smallEtaleStagesFull_of_isTrivialized B Dg c hX hc haff hqc hqs _
    (smallEtaleConstantMapsLocallyConstant_type B) (smallEtaleConstantFaithful_type B) _
    fun X F hF => (isTrivialized_iff_isFiniteLocallyConstant B (Type (u + 1)) X F).mpr hF

/-- **Tag 0GL2 (2), faithfulness.** Two maps between finite locally constant abelian sheaves at
a stage which agree after inverse image to the limit agree at a later stage. -/
public theorem smallEtaleStagesFaithful_isFiniteLocallyConstant_addCommGrpCat (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj)
    (hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj) :
    SmallEtaleStagesFaithful B AddCommGrpCat.{u + 1} Dg c hX
      (isFiniteLocallyConstantSmallEtaleSheaf B AddCommGrpCat.{u + 1}) :=
  smallEtaleStagesFaithful_of_isTrivialized B Dg c hX hc haff hqc hqs _
    (smallEtaleConstantMapsLocallyConstant_addCommGrpCat B)
    (smallEtaleConstantFaithful_addCommGrpCat B) _
    fun X F hF => (isTrivialized_iff_isFiniteLocallyConstant B AddCommGrpCat.{u + 1} X F).mpr hF

/-- **Tag 0GL2 (2), fullness.** Every map between the inverse images to the limit of two finite
locally constant abelian sheaves at a stage comes from a map at a later stage. -/
public theorem smallEtaleStagesFull_isFiniteLocallyConstant_addCommGrpCat (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj)
    (hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj) :
    SmallEtaleStagesFull B AddCommGrpCat.{u + 1} Dg c hX
      (isFiniteLocallyConstantSmallEtaleSheaf B AddCommGrpCat.{u + 1}) :=
  smallEtaleStagesFull_of_isTrivialized B Dg c hX hc haff hqc hqs _
    (smallEtaleConstantMapsLocallyConstant_addCommGrpCat B)
    (smallEtaleConstantFaithful_addCommGrpCat B) _
    fun X F hF => (isTrivialized_iff_isFiniteLocallyConstant B AddCommGrpCat.{u + 1} X F).mpr hF

/-- **Tag 0GL2 (3), faithfulness.** Two maps between finite type locally constant sheaves of
`Λ`-modules at a stage which agree after inverse image to the limit agree at a later stage. -/
public theorem smallEtaleStagesFaithful_isFiniteTypeLocallyConstant (Λ : Type (u + 1))
    [CommRing Λ] (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj)
    (hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj) :
    SmallEtaleStagesFaithful B (ModuleCat.{u + 1} Λ) Dg c hX
      (isFiniteTypeLocallyConstantSmallEtaleSheaf B Λ) :=
  smallEtaleStagesFaithful_of_isTrivialized B Dg c hX hc haff hqc hqs _
    (smallEtaleConstantMapsLocallyConstant_moduleCat B Λ) (smallEtaleConstantFaithful_moduleCat B Λ)
    _ fun _ _ hF => hF

/-- **Tag 0GL2 (3), fullness.** Every map between the inverse images to the limit of two finite
type locally constant sheaves of `Λ`-modules at a stage comes from a map at a later stage. -/
public theorem smallEtaleStagesFull_isFiniteTypeLocallyConstant (Λ : Type (u + 1))
    [CommRing Λ] (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj)
    (hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj) :
    SmallEtaleStagesFull B (ModuleCat.{u + 1} Λ) Dg c hX
      (isFiniteTypeLocallyConstantSmallEtaleSheaf B Λ) :=
  smallEtaleStagesFull_of_isTrivialized B Dg c hX hc haff hqc hqs _
    (smallEtaleConstantMapsLocallyConstant_moduleCat B Λ) (smallEtaleConstantFaithful_moduleCat B Λ)
    _ fun _ _ hF => hF

end Concrete

end AlgebraicGeometry

end
