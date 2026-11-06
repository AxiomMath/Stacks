module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantLimit.Constants

/-!
# Essential surjectivity for finite locally constant sheaves along a limit of schemes

Let `X = lim X_i` be the limit of a directed inverse system of quasi-compact, quasi-separated
schemes with affine transition morphisms inside a big étale site. This file proves the essential
surjectivity half of Stacks Tag 0GL2: every finite locally constant sheaf on `X_étale` (of sets,
of abelian groups, or of finite type of `Λ`-modules) is the inverse image of a finite locally
constant sheaf at some stage `X_i`.

## Strategy

Let `F` be trivialized on a covering of `X`. The covering is refined by the base changes
`W_n ×_{X_j} X` of a finite affine étale covering `{W_n}` of a stage `X_j` (Tag 0EYL), so `F` is
the constant sheaf on a value `E_n` over each `W_n ×_{X_j} X`. Over the overlaps
`(W_n ×_{X_j} W_m) ×_{X_j} X` the two trivializations differ by an isomorphism of constant
sheaves; these transitions satisfy the cocycle condition on the triple overlaps. The overlaps and
triple overlaps are the vertices of the member systems `J ↦ (W_n ×_{X_j} W_m) ×_{X_j} X_J`,
which are again limit systems, so the transitions come from a stage and the cocycle condition
holds at a later stage (the case of constant sheaves,
`AlgebraicGeometry.exists_stage_transport_iso` and
`AlgebraicGeometry.exists_stage_transport_eq_of_transport_eq`). There the constant sheaves glue
to a sheaf `F_J` (`AlgebraicGeometry.smallEtaleSheaf_exists_glue_constant_of_isPullback`), which
is trivialized, hence finite locally constant. Its inverse image to `X` and `F` are trivialized on
the same covering of `X` with the same transitions, so they are isomorphic
(`AlgebraicGeometry.smallEtaleSheafPullback_exists_map_eq_of_isPullback` and
`AlgebraicGeometry.smallEtaleSheafPullback_jointly_faithful`).

Trivializations are handled through their restrictions along morphisms,
`AlgebraicGeometry.smallEtaleTrivializationRestrict`, and transitions are compared through
transport of morphisms of constant sheaves, `AlgebraicGeometry.smallEtaleConstantTransport`.
Overlaps of base changes are base changes of overlaps; all overlaps and triple overlaps are
fibre products named by `AlgebraicGeometry.smallEtaleOverlapObj` and
`AlgebraicGeometry.smallEtaleTripleObj`, so that the member systems apply to them literally.

## Main results

* `AlgebraicGeometry.smallEtaleStagesEssSurj_isTrivialized` — essential surjectivity for sheaves
  trivialized with values satisfying a property `P`, for a coefficient category in which
  morphisms of constant sheaves with source satisfying `P` are locally constant and the constant
  sheaf functor is faithful over nonempty schemes.
* `AlgebraicGeometry.smallEtaleStagesEssSurj_isFiniteLocallyConstant_type`,
  `AlgebraicGeometry.smallEtaleStagesEssSurj_isFiniteLocallyConstant_addCommGrpCat` and
  `AlgebraicGeometry.smallEtaleStagesEssSurj_isFiniteTypeLocallyConstant_moduleCat` — the
  essential surjectivity halves of the three clauses of Tag 0GL2.

## References

* [Stacks Project, Tag 0GL2](https://stacks.math.columbia.edu/tag/0GL2)
* [Stacks Project, Tag 0EYL](https://stacks.math.columbia.edu/tag/0EYL)
* [Stacks Project, Tag 04TR](https://stacks.math.columbia.edu/tag/04TR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe t v u

namespace AlgebraicGeometry

section Restrict

variable (B : BigEtaleSite.{u}) (A : Type t) [Category.{v} A]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous A
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (S : B.Scheme), HasWeakSheafify (SmallEtale.topology B S.obj S.property) A]

/-- **Restriction of a trivialization.** A trivialization `ε` of the inverse image of `F` along
`s : T ⟶ S` as the constant sheaf on `E`, restricted along `a : Y ⟶ T`: a trivialization of the
inverse image of `F` along the named composite `r = a ≫ s`. -/
public def smallEtaleTrivializationRestrict {S T Y : B.Scheme}
    {F : Sheaf (SmallEtale.topology B S.obj S.property) A} {s : T ⟶ S} {E : A}
    (ε : (smallEtaleSheafPullback B A s).obj F ≅
      (constantSheaf (SmallEtale.topology B T.obj T.property) A).obj E)
    (a : Y ⟶ T) (r : Y ⟶ S) (h : a ≫ s = r) :
    (smallEtaleSheafPullback B A r).obj F ≅
      (constantSheaf (SmallEtale.topology B Y.obj Y.property) A).obj E :=
  ((smallEtaleSheafPullbackCompIso' B A a s r h).app F).symm ≪≫
    (smallEtaleSheafPullback B A a).mapIso ε ≪≫ smallEtaleConstantPullbackIso B A a E

variable {B A}

/-- **Restrictions of trivializations compose.** -/
public theorem smallEtaleTrivializationRestrict_restrict {S T Y Y' : B.Scheme}
    {F : Sheaf (SmallEtale.topology B S.obj S.property) A} {s : T ⟶ S} {E : A}
    (ε : (smallEtaleSheafPullback B A s).obj F ≅
      (constantSheaf (SmallEtale.topology B T.obj T.property) A).obj E)
    (a : Y ⟶ T) (r : Y ⟶ S) (h : a ≫ s = r) (g : Y' ⟶ Y) (r' : Y' ⟶ S)
    (hr : g ≫ r = r') (ga : Y' ⟶ T) (hga : g ≫ a = ga) (h' : ga ≫ s = r') :
    smallEtaleTrivializationRestrict B A (smallEtaleTrivializationRestrict B A ε a r h) g r' hr =
      smallEtaleTrivializationRestrict B A ε ga r' h' := by
  ext1
  have h1 := smallEtaleSheafPullbackCompIso'_assoc B A g a s ga r r' hga h h' hr F
  have h1' : (smallEtaleSheafPullbackCompIso' B A g r r' hr).inv.app F ≫
      (smallEtaleSheafPullback B A g).map
        ((smallEtaleSheafPullbackCompIso' B A a s r h).inv.app F) =
      (smallEtaleSheafPullbackCompIso' B A ga s r' h').inv.app F ≫
      (smallEtaleSheafPullbackCompIso' B A g a ga hga).inv.app
        ((smallEtaleSheafPullback B A s).obj F) := by
    rw [← cancel_epi ((smallEtaleSheafPullbackCompIso' B A g r r' hr).hom.app F),
      Iso.hom_inv_id_app_assoc,
      ← cancel_epi ((smallEtaleSheafPullback B A g).map
        ((smallEtaleSheafPullbackCompIso' B A a s r h).hom.app F)),
      ← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, reassoc_of% h1,
      Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app]
    rfl
  have h2 := (smallEtaleSheafPullbackCompIso' B A g a ga hga).inv.naturality ε.hom
  have h3 := smallEtaleSheafPullbackCompIso'_inv_app_constantSheaf B A g a ga hga E
  simp only [Functor.comp_map] at h2
  simp only [smallEtaleTrivializationRestrict, Iso.trans_hom, Iso.symm_hom, Iso.app_inv,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [reassoc_of% h1', ← reassoc_of% h2, h3]

/-- Restriction along equal morphisms. -/
public theorem smallEtaleTrivializationRestrict_congr {S T Y : B.Scheme}
    {F : Sheaf (SmallEtale.topology B S.obj S.property) A} {s : T ⟶ S} {E : A}
    (ε : (smallEtaleSheafPullback B A s).obj F ≅
      (constantSheaf (SmallEtale.topology B T.obj T.property) A).obj E)
    {a a' : Y ⟶ T} (r : Y ⟶ S) (h : a ≫ s = r) (h' : a' ≫ s = r) (e : a = a') :
    smallEtaleTrivializationRestrict B A ε a r h =
      smallEtaleTrivializationRestrict B A ε a' r h' := by
  subst e
  rfl

/-- **The transition between two restricted trivializations is the transport of the transition
between the trivializations.** -/
public theorem smallEtaleTrivializationRestrict_inv_hom {S T Y : B.Scheme}
    {F : Sheaf (SmallEtale.topology B S.obj S.property) A} {s : T ⟶ S} {E₁ E₂ : A}
    (ε₁ : (smallEtaleSheafPullback B A s).obj F ≅
      (constantSheaf (SmallEtale.topology B T.obj T.property) A).obj E₁)
    (ε₂ : (smallEtaleSheafPullback B A s).obj F ≅
      (constantSheaf (SmallEtale.topology B T.obj T.property) A).obj E₂)
    (a : Y ⟶ T) (r : Y ⟶ S) (h h' : a ≫ s = r) :
    (smallEtaleTrivializationRestrict B A ε₁ a r h).inv ≫
        (smallEtaleTrivializationRestrict B A ε₂ a r h').hom =
      smallEtaleConstantTransport B A a (ε₁.inv ≫ ε₂.hom) := by
  simp [smallEtaleTrivializationRestrict, smallEtaleConstantTransport]

/-- **Restriction of transitions.** -/
public theorem smallEtaleConstantTransport_restrict_inv_hom {S T₁ T₂ Y Y' : B.Scheme}
    {F : Sheaf (SmallEtale.topology B S.obj S.property) A} {s₁ : T₁ ⟶ S} {s₂ : T₂ ⟶ S}
    {E₁ E₂ : A}
    (ε₁ : (smallEtaleSheafPullback B A s₁).obj F ≅
      (constantSheaf (SmallEtale.topology B T₁.obj T₁.property) A).obj E₁)
    (ε₂ : (smallEtaleSheafPullback B A s₂).obj F ≅
      (constantSheaf (SmallEtale.topology B T₂.obj T₂.property) A).obj E₂)
    (a : Y ⟶ T₁) (b : Y ⟶ T₂) (r : Y ⟶ S) (ha : a ≫ s₁ = r) (hb : b ≫ s₂ = r)
    (g : Y' ⟶ Y) (r' : Y' ⟶ S) (hr : g ≫ r = r') (ga : Y' ⟶ T₁) (hga : g ≫ a = ga)
    (gb : Y' ⟶ T₂) (hgb : g ≫ b = gb) (ha' : ga ≫ s₁ = r') (hb' : gb ≫ s₂ = r') :
    smallEtaleConstantTransport B A g
        ((smallEtaleTrivializationRestrict B A ε₁ a r ha).inv ≫
          (smallEtaleTrivializationRestrict B A ε₂ b r hb).hom) =
      (smallEtaleTrivializationRestrict B A ε₁ ga r' ha').inv ≫
        (smallEtaleTrivializationRestrict B A ε₂ gb r' hb').hom := by
  rw [← smallEtaleTrivializationRestrict_inv_hom _ _ g r' hr hr,
    smallEtaleTrivializationRestrict_restrict ε₁ a r ha g r' hr ga hga ha',
    smallEtaleTrivializationRestrict_restrict ε₂ b r hb g r' hr gb hgb hb']

/-- **Restriction of a trivialization of an inverse image.** -/
public theorem smallEtaleTrivializationRestrict_pullback {S T Y Y₀ : B.Scheme}
    {G : Sheaf (SmallEtale.topology B Y₀.obj Y₀.property) A} (k : S ⟶ Y₀) {s : T ⟶ S}
    (sk : T ⟶ Y₀) (e₀ : s ≫ k = sk) {E : A}
    (θ : (smallEtaleSheafPullback B A sk).obj G ≅
      (constantSheaf (SmallEtale.topology B T.obj T.property) A).obj E)
    (a : Y ⟶ T) (r : Y ⟶ S) (h : a ≫ s = r) (rk : Y ⟶ Y₀) (e₁ : r ≫ k = rk)
    (e₂ : a ≫ sk = rk) :
    smallEtaleTrivializationRestrict B A
        (((smallEtaleSheafPullbackCompIso' B A s k sk e₀).app G) ≪≫ θ) a r h =
      ((smallEtaleSheafPullbackCompIso' B A r k rk e₁).app G) ≪≫
        smallEtaleTrivializationRestrict B A θ a rk e₂ := by
  ext1
  have h1 := smallEtaleSheafPullbackCompIso'_assoc B A a s k r sk rk h e₀ e₁ e₂ G
  have h1' : (smallEtaleSheafPullbackCompIso' B A a s r h).inv.app
        ((smallEtaleSheafPullback B A k).obj G) ≫
      (smallEtaleSheafPullback B A a).map
        ((smallEtaleSheafPullbackCompIso' B A s k sk e₀).hom.app G) =
      (smallEtaleSheafPullbackCompIso' B A r k rk e₁).hom.app G ≫
      (smallEtaleSheafPullbackCompIso' B A a sk rk e₂).inv.app G := by
    rw [← cancel_epi ((smallEtaleSheafPullbackCompIso' B A a s r h).hom.app
        ((smallEtaleSheafPullback B A k).obj G)), Iso.hom_inv_id_app_assoc,
      ← reassoc_of% h1, Iso.hom_inv_id_app]
    exact (Category.comp_id _).symm
  simp only [smallEtaleTrivializationRestrict, Iso.trans_hom, Iso.symm_hom, Iso.app_inv,
    Iso.app_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [reassoc_of% h1']

/-- **The gluing condition for morphisms, in terms of trivializations.** -/
public theorem smallEtaleSheafPullbackCompIso'_conj_trivialization {S T Y : B.Scheme}
    {F F' : Sheaf (SmallEtale.topology B S.obj S.property) A} {s : T ⟶ S} {E : A}
    (δ : (smallEtaleSheafPullback B A s).obj F ≅
      (constantSheaf (SmallEtale.topology B T.obj T.property) A).obj E)
    (ε : (smallEtaleSheafPullback B A s).obj F' ≅
      (constantSheaf (SmallEtale.topology B T.obj T.property) A).obj E)
    (a : Y ⟶ T) (r : Y ⟶ S) (h : a ≫ s = r) :
    (smallEtaleSheafPullbackCompIso' B A a s r h).inv.app F ≫
        (smallEtaleSheafPullback B A a).map (δ.hom ≫ ε.inv) ≫
        (smallEtaleSheafPullbackCompIso' B A a s r h).hom.app F' =
      (smallEtaleTrivializationRestrict B A δ a r h).hom ≫
        (smallEtaleTrivializationRestrict B A ε a r h).inv := by
  simp [smallEtaleTrivializationRestrict]

end Restrict

section Overlap

variable (B : BigEtaleSite.{u})

/-- The first projection of a fibre product along an étale morphism is étale. -/
public theorem etale_inclusion_map_pullback_fst {X Y Z : B.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z)
    [Etale (B.inclusion.map g)] : Etale (B.inclusion.map (pullback.fst f g)) :=
  MorphismProperty.of_isPullback ((IsPullback.of_hasPullback f g).map B.inclusion).flip
    ‹Etale (B.inclusion.map g)›

attribute [local instance] etale_inclusion_map_pullback_fst

/-- A fibre product of schemes of a big étale site over a quasi-separated scheme of two
quasi-compact schemes is quasi-compact. -/
public theorem compactSpace_pullback_bigEtale {X Y Z : B.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z)
    [CompactSpace X.obj] [CompactSpace Y.obj] [QuasiSeparatedSpace Z.obj] :
    CompactSpace (pullback f g).obj := by
  have : CompactSpace (B.inclusion.obj Y) := ‹CompactSpace Y.obj›
  have : CompactSpace (B.inclusion.obj X) := ‹CompactSpace X.obj›
  have : QuasiSeparatedSpace (B.inclusion.obj Z) := ‹QuasiSeparatedSpace Z.obj›
  have : QuasiCompact (B.inclusion.map (pullback.fst f g)) :=
    MorphismProperty.of_isPullback ((IsPullback.of_hasPullback f g).map B.inclusion).flip
      (inferInstance : QuasiCompact (B.inclusion.map g))
  exact QuasiCompact.compactSpace_of_compactSpace (B.inclusion.map (pullback.fst f g))

/-- A fibre product of two quasi-separated schemes of a big étale site is quasi-separated. -/
public theorem quasiSeparatedSpace_pullback_bigEtale {X Y Z : B.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z)
    [QuasiSeparatedSpace X.obj] [QuasiSeparatedSpace Y.obj] :
    QuasiSeparatedSpace (pullback f g).obj := by
  have : QuasiSeparatedSpace (B.inclusion.obj Y) := ‹QuasiSeparatedSpace Y.obj›
  have : QuasiSeparatedSpace (B.inclusion.obj X) := ‹QuasiSeparatedSpace X.obj›
  have : QuasiSeparated (B.inclusion.map (pullback.fst f g)) :=
    MorphismProperty.of_isPullback ((IsPullback.of_hasPullback f g).map B.inclusion).flip
      (inferInstance : QuasiSeparated (B.inclusion.map g))
  exact quasiSeparatedSpace_of_quasiSeparated (B.inclusion.map (pullback.fst f g))

variable {S : B.Scheme}

/-- The overlap `Z₁ ×_S Z₂` of two objects of the small étale site of `S`, as an object of that
site through the first factor. -/
public abbrev smallEtaleOverlapObj (Z₁ Z₂ : SmallEtale B S.obj S.property) :
    SmallEtale B S.obj S.property :=
  ⟨Over.mk (pullback.fst Z₁.obj.hom Z₂.obj.hom ≫ Z₁.obj.hom), by
    change Etale (B.inclusion.map (pullback.fst Z₁.obj.hom Z₂.obj.hom ≫ Z₁.obj.hom))
    rw [B.inclusion.map_comp]
    infer_instance⟩

variable {T : B.Scheme} (f : T ⟶ S)

/-- The base change along `f : T ⟶ S` of a morphism between objects of the small étale site
of `S` (as schemes over `S`). -/
public def smallEtaleBaseChangeMap {Z Z' : SmallEtale B S.obj S.property}
    (φ : Z.obj.left ⟶ Z'.obj.left)
    (hφ : φ ≫ Z'.obj.hom = Z.obj.hom) : pullback Z.obj.hom f ⟶ pullback Z'.obj.hom f :=
  pullback.map _ _ _ _ φ (𝟙 T) (𝟙 S) (by rw [Category.comp_id, hφ])
    (by rw [Category.comp_id, Category.id_comp])

/-- A base change map is the given morphism on the first component. -/
@[reassoc (attr := simp)]
public theorem smallEtaleBaseChangeMap_fst {Z Z' : SmallEtale B S.obj S.property}
    (φ : Z.obj.left ⟶ Z'.obj.left) (hφ : φ ≫ Z'.obj.hom = Z.obj.hom) :
    smallEtaleBaseChangeMap B f φ hφ ≫ pullback.fst Z'.obj.hom f = pullback.fst Z.obj.hom f ≫ φ :=
  pullback.lift_fst _ _ _

/-- A base change map is the identity on the second component. -/
@[reassoc (attr := simp)]
public theorem smallEtaleBaseChangeMap_snd {Z Z' : SmallEtale B S.obj S.property}
    (φ : Z.obj.left ⟶ Z'.obj.left) (hφ : φ ≫ Z'.obj.hom = Z.obj.hom) :
    smallEtaleBaseChangeMap B f φ hφ ≫ pullback.snd Z'.obj.hom f = pullback.snd Z.obj.hom f :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- Base change maps compose. -/
public theorem smallEtaleBaseChangeMap_comp {Z Z' Z'' : SmallEtale B S.obj S.property}
    (φ : Z.obj.left ⟶ Z'.obj.left) (hφ : φ ≫ Z'.obj.hom = Z.obj.hom)
    (ψ : Z'.obj.left ⟶ Z''.obj.left) (hψ : ψ ≫ Z''.obj.hom = Z'.obj.hom)
    (χ : Z.obj.left ⟶ Z''.obj.left) (hχ : χ ≫ Z''.obj.hom = Z.obj.hom) (h : φ ≫ ψ = χ) :
    smallEtaleBaseChangeMap B f φ hφ ≫ smallEtaleBaseChangeMap B f ψ hψ =
      smallEtaleBaseChangeMap B f χ hχ := by
  apply pullback.hom_ext
  · rw [Category.assoc, smallEtaleBaseChangeMap_fst, smallEtaleBaseChangeMap_fst_assoc,
      smallEtaleBaseChangeMap_fst, h]
  · rw [Category.assoc, smallEtaleBaseChangeMap_snd, smallEtaleBaseChangeMap_snd,
      smallEtaleBaseChangeMap_snd]

/-- The base change of a morphism is cartesian over it. -/
public theorem isPullback_smallEtaleBaseChangeMap_fst {Z Z' : SmallEtale B S.obj S.property}
    (φ : Z.obj.left ⟶ Z'.obj.left) (hφ : φ ≫ Z'.obj.hom = Z.obj.hom) :
    IsPullback (smallEtaleBaseChangeMap B f φ hφ) (pullback.fst Z.obj.hom f)
      (pullback.fst Z'.obj.hom f) φ := by
  refine IsPullback.of_right ?_ (smallEtaleBaseChangeMap_fst B f φ hφ)
    (IsPullback.of_hasPullback Z'.obj.hom f).flip
  rw [smallEtaleBaseChangeMap_snd, hφ]
  exact (IsPullback.of_hasPullback Z.obj.hom f).flip

/-- **The base change of a cartesian square over `S` is cartesian over `T`.** -/
public theorem isPullback_smallEtaleBaseChangeMap_of_isPullback
    {P Z₁ Z₂ : SmallEtale B S.obj S.property}
    (a : P.obj.left ⟶ Z₁.obj.left) (ha : a ≫ Z₁.obj.hom = P.obj.hom)
    (b : P.obj.left ⟶ Z₂.obj.left) (hb : b ≫ Z₂.obj.hom = P.obj.hom)
    (sq : IsPullback a b Z₁.obj.hom Z₂.obj.hom) :
    IsPullback (smallEtaleBaseChangeMap B f a ha) (smallEtaleBaseChangeMap B f b hb)
      (pullback.snd Z₁.obj.hom f) (pullback.snd Z₂.obj.hom f) := by
  refine (IsPullback.of_right ?_ (by rw [smallEtaleBaseChangeMap_snd, smallEtaleBaseChangeMap_snd])
    (IsPullback.of_hasPullback Z₂.obj.hom f)).flip
  rw [smallEtaleBaseChangeMap_fst, ← pullback.condition]
  exact (isPullback_smallEtaleBaseChangeMap_fst B f a ha).flip.paste_horiz sq.flip

/-- **The base change of a cartesian square of objects over `S` is cartesian.** -/
public theorem isPullback_smallEtaleBaseChangeMap_of_isPullback'
    {P Z₁ Z₂ Y : SmallEtale B S.obj S.property}
    (a : P.obj.left ⟶ Z₁.obj.left) (ha : a ≫ Z₁.obj.hom = P.obj.hom)
    (b : P.obj.left ⟶ Z₂.obj.left) (hb : b ≫ Z₂.obj.hom = P.obj.hom)
    (g₁ : Z₁.obj.left ⟶ Y.obj.left) (hg₁ : g₁ ≫ Y.obj.hom = Z₁.obj.hom)
    (g₂ : Z₂.obj.left ⟶ Y.obj.left) (hg₂ : g₂ ≫ Y.obj.hom = Z₂.obj.hom)
    (sq : IsPullback a b g₁ g₂) :
    IsPullback (smallEtaleBaseChangeMap B f a ha) (smallEtaleBaseChangeMap B f b hb)
      (smallEtaleBaseChangeMap B f g₁ hg₁) (smallEtaleBaseChangeMap B f g₂ hg₂) := by
  refine (IsPullback.of_right ?_ ?_ (isPullback_smallEtaleBaseChangeMap_fst B f g₂ hg₂).flip).flip
  · rw [smallEtaleBaseChangeMap_fst, smallEtaleBaseChangeMap_fst]
    exact (isPullback_smallEtaleBaseChangeMap_fst B f a ha).flip.paste_horiz sq.flip
  · rw [smallEtaleBaseChangeMap_comp B f b hb g₂ hg₂ (b ≫ g₂) (by rw [Category.assoc, hg₂, hb])
      rfl, smallEtaleBaseChangeMap_comp B f a ha g₁ hg₁ (b ≫ g₂)
        (by rw [Category.assoc, hg₂, hb]) sq.w]

/-- Two composites of base change maps of equal composites agree. -/
public theorem smallEtaleBaseChangeMap_comp_eq {Z Z₁ Z₂ Z' : SmallEtale B S.obj S.property}
    (φ₁ : Z.obj.left ⟶ Z₁.obj.left) (hφ₁ : φ₁ ≫ Z₁.obj.hom = Z.obj.hom)
    (ψ₁ : Z₁.obj.left ⟶ Z'.obj.left) (hψ₁ : ψ₁ ≫ Z'.obj.hom = Z₁.obj.hom)
    (φ₂ : Z.obj.left ⟶ Z₂.obj.left) (hφ₂ : φ₂ ≫ Z₂.obj.hom = Z.obj.hom)
    (ψ₂ : Z₂.obj.left ⟶ Z'.obj.left) (hψ₂ : ψ₂ ≫ Z'.obj.hom = Z₂.obj.hom)
    (h : φ₁ ≫ ψ₁ = φ₂ ≫ ψ₂) :
    smallEtaleBaseChangeMap B f φ₁ hφ₁ ≫ smallEtaleBaseChangeMap B f ψ₁ hψ₁ =
      smallEtaleBaseChangeMap B f φ₂ hφ₂ ≫ smallEtaleBaseChangeMap B f ψ₂ hψ₂ := by
  rw [smallEtaleBaseChangeMap_comp B f φ₁ hφ₁ ψ₁ hψ₁ (φ₁ ≫ ψ₁)
      (by rw [Category.assoc, hψ₁, hφ₁]) rfl,
    smallEtaleBaseChangeMap_comp B f φ₂ hφ₂ ψ₂ hψ₂ (φ₁ ≫ ψ₁)
      (by rw [Category.assoc, hψ₁, hφ₁]) h.symm]

variable {T' : B.Scheme} (f' : T' ⟶ S) (g : T' ⟶ T) (hg : g ≫ f = f')

/-- The base change of an object of the small étale site along a morphism over `S`. -/
public def memberBaseChangeMap (W : SmallEtale B S.obj S.property) :
    pullback W.obj.hom f' ⟶ pullback W.obj.hom f :=
  pullback.map _ _ _ _ (𝟙 _) g (𝟙 S) (by rw [Category.comp_id, Category.id_comp])
    (by rw [Category.comp_id, hg])

/-- The base change of an object along a morphism over `S` is the identity on the first
component. -/
@[reassoc (attr := simp)]
public theorem memberBaseChangeMap_fst (W : SmallEtale B S.obj S.property) :
    memberBaseChangeMap B f f' g hg W ≫ pullback.fst W.obj.hom f = pullback.fst W.obj.hom f' :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

/-- The base change of an object along a morphism over `S` is that morphism on the second
component. -/
@[reassoc (attr := simp)]
public theorem memberBaseChangeMap_snd (W : SmallEtale B S.obj S.property) :
    memberBaseChangeMap B f f' g hg W ≫ pullback.snd W.obj.hom f =
      pullback.snd W.obj.hom f' ≫ g :=
  pullback.lift_snd _ _ _

/-- Base change maps of objects commute with base change maps of morphisms. -/
@[reassoc]
public theorem memberBaseChangeMap_smallEtaleBaseChangeMap {Z Z' : SmallEtale B S.obj S.property}
    (φ : Z.obj.left ⟶ Z'.obj.left) (hφ : φ ≫ Z'.obj.hom = Z.obj.hom) :
    memberBaseChangeMap B f f' g hg Z ≫ smallEtaleBaseChangeMap B f φ hφ =
      smallEtaleBaseChangeMap B f' φ hφ ≫ memberBaseChangeMap B f f' g hg Z' := by
  apply pullback.hom_ext
  · rw [Category.assoc, smallEtaleBaseChangeMap_fst, memberBaseChangeMap_fst_assoc, Category.assoc,
      memberBaseChangeMap_fst, smallEtaleBaseChangeMap_fst]
  · rw [Category.assoc, smallEtaleBaseChangeMap_snd, memberBaseChangeMap_snd, Category.assoc,
      memberBaseChangeMap_snd, smallEtaleBaseChangeMap_snd_assoc]

end Overlap

section Transport

variable {B : BigEtaleSite.{u}} {A : Type t} [Category.{v} A]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous A
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (S : B.Scheme), HasWeakSheafify (SmallEtale.topology B S.obj S.property) A]

/-- Transport along the two sides of a commutative square agree. -/
public theorem smallEtaleConstantTransport_square {X Y Y' Z : B.Scheme} (x : X ⟶ Y)
    (y : Y ⟶ Z) (x' : X ⟶ Y') (y' : Y' ⟶ Z) (h : x ≫ y = x' ≫ y') {E E' : A}
    (a : (constantSheaf (SmallEtale.topology B Z.obj Z.property) A).obj E ⟶
      (constantSheaf (SmallEtale.topology B Z.obj Z.property) A).obj E') :
    smallEtaleConstantTransport B A x (smallEtaleConstantTransport B A y a) =
      smallEtaleConstantTransport B A x' (smallEtaleConstantTransport B A y' a) := by
  rw [← smallEtaleConstantTransport_comp' B A x y _ rfl,
    ← smallEtaleConstantTransport_comp' B A x' y' _ rfl, h]

/-- **The transitions of trivializations pulled back from a later stage.** -/
public theorem smallEtaleTrivialization_transition_pullback {S Y₀ Un Um Vn Vm Z O : B.Scheme}
    (k : S ⟶ Y₀) {G : Sheaf (SmallEtale.topology B Y₀.obj Y₀.property) A}
    {vn : Vn ⟶ Y₀} {vm : Vm ⟶ Y₀} {En Em : A}
    (ηn : (smallEtaleSheafPullback B A vn).obj G ≅
      (constantSheaf (SmallEtale.topology B Vn.obj Vn.property) A).obj En)
    (ηm : (smallEtaleSheafPullback B A vm).obj G ≅
      (constantSheaf (SmallEtale.topology B Vm.obj Vm.property) A).obj Em)
    (sn : Un ⟶ S) (sm : Um ⟶ S) (μn : Un ⟶ Vn) (μm : Um ⟶ Vm)
    (hμn : μn ≫ vn = sn ≫ k) (hμm : μm ≫ vm = sm ≫ k)
    (a : Z ⟶ Un) (b : Z ⟶ Um) (r : Z ⟶ S) (ha : a ≫ sn = r) (hb : b ≫ sm = r)
    (p : O ⟶ Vn) (q : O ⟶ Vm) (r₀ : O ⟶ Y₀) (hp : p ≫ vn = r₀) (hq : q ≫ vm = r₀)
    (ν : Z ⟶ O) (hνp : a ≫ μn = ν ≫ p) (hνq : b ≫ μm = ν ≫ q) (hν : ν ≫ r₀ = r ≫ k) :
    (smallEtaleTrivializationRestrict B A
        (((smallEtaleSheafPullbackCompIso' B A sm k (sm ≫ k) rfl).app G) ≪≫
          smallEtaleTrivializationRestrict B A ηm μm (sm ≫ k) hμm) b r hb).inv ≫
      (smallEtaleTrivializationRestrict B A
        (((smallEtaleSheafPullbackCompIso' B A sn k (sn ≫ k) rfl).app G) ≪≫
          smallEtaleTrivializationRestrict B A ηn μn (sn ≫ k) hμn) a r ha).hom =
    smallEtaleConstantTransport B A ν
      ((smallEtaleTrivializationRestrict B A ηm q r₀ hq).inv ≫
        (smallEtaleTrivializationRestrict B A ηn p r₀ hp).hom) := by
  rw [smallEtaleTrivializationRestrict_pullback k (sn ≫ k) rfl _ a r ha (r ≫ k) rfl
      (by rw [← Category.assoc, ha]),
    smallEtaleTrivializationRestrict_pullback k (sm ≫ k) rfl _ b r hb (r ≫ k) rfl
      (by rw [← Category.assoc, hb]),
    smallEtaleTrivializationRestrict_restrict ηn μn (sn ≫ k) hμn a (r ≫ k) _ (ν ≫ p) hνp
      (by rw [Category.assoc, hp, hν]),
    smallEtaleTrivializationRestrict_restrict ηm μm (sm ≫ k) hμm b (r ≫ k) _ (ν ≫ q) hνq
      (by rw [Category.assoc, hq, hν]),
    ← smallEtaleTrivializationRestrict_restrict ηn p r₀ hp ν (r ≫ k) hν (ν ≫ p) rfl
      (by rw [Category.assoc, hp, hν]),
    ← smallEtaleTrivializationRestrict_restrict ηm q r₀ hq ν (r ≫ k) hν (ν ≫ q) rfl
      (by rw [Category.assoc, hq, hν]),
    ← smallEtaleTrivializationRestrict_inv_hom _ _ ν (r ≫ k) hν hν]
  simp

end Transport

section Triple

variable (B : BigEtaleSite.{u}) {S : B.Scheme}

attribute [local instance] etale_inclusion_map_pullback_fst

/-- The triple overlap `W₁ ×_S W₂ ×_S W₃` of three objects of the small étale site of `S`, as the
fibre product of the overlaps `W₁ ×_S W₂` and `W₂ ×_S W₃` over `W₂`. -/
public abbrev smallEtaleTripleObj (W₁ W₂ W₃ : SmallEtale B S.obj S.property) :
    SmallEtale B S.obj S.property :=
  ⟨Over.mk (pullback.fst (pullback.snd W₁.obj.hom W₂.obj.hom)
      (pullback.fst W₂.obj.hom W₃.obj.hom) ≫ pullback.fst W₁.obj.hom W₂.obj.hom ≫ W₁.obj.hom),
    by
      change Etale (B.inclusion.map (pullback.fst (pullback.snd W₁.obj.hom W₂.obj.hom)
        (pullback.fst W₂.obj.hom W₃.obj.hom) ≫ pullback.fst W₁.obj.hom W₂.obj.hom ≫ W₁.obj.hom))
      rw [B.inclusion.map_comp, B.inclusion.map_comp]
      infer_instance⟩

variable (W₁ W₂ W₃ : SmallEtale B S.obj S.property)

/-- The projection of a triple overlap to the overlap of the first two members. -/
public abbrev tripleFst :
    (smallEtaleTripleObj B W₁ W₂ W₃).obj.left ⟶ (smallEtaleOverlapObj B W₁ W₂).obj.left :=
  pullback.fst (pullback.snd W₁.obj.hom W₂.obj.hom) (pullback.fst W₂.obj.hom W₃.obj.hom)

/-- The projection of a triple overlap to the overlap of the last two members. -/
public abbrev tripleSnd :
    (smallEtaleTripleObj B W₁ W₂ W₃).obj.left ⟶ (smallEtaleOverlapObj B W₂ W₃).obj.left :=
  pullback.snd (pullback.snd W₁.obj.hom W₂.obj.hom) (pullback.fst W₂.obj.hom W₃.obj.hom)

/-- The two maps of a triple overlap to the middle member agree. -/
public theorem tripleFst_snd :
    tripleFst B W₁ W₂ W₃ ≫ pullback.snd W₁.obj.hom W₂.obj.hom =
      tripleSnd B W₁ W₂ W₃ ≫ pullback.fst W₂.obj.hom W₃.obj.hom :=
  pullback.condition

/-- The first projection of a triple overlap is a morphism over `S`. -/
public theorem tripleFst_hom :
    tripleFst B W₁ W₂ W₃ ≫ (smallEtaleOverlapObj B W₁ W₂).obj.hom =
      (smallEtaleTripleObj B W₁ W₂ W₃).obj.hom := rfl

/-- The second projection of a triple overlap is a morphism over `S`. -/
public theorem tripleSnd_hom :
    tripleSnd B W₁ W₂ W₃ ≫ (smallEtaleOverlapObj B W₂ W₃).obj.hom =
      (smallEtaleTripleObj B W₁ W₂ W₃).obj.hom := by
  show tripleSnd B W₁ W₂ W₃ ≫ pullback.fst W₂.obj.hom W₃.obj.hom ≫ W₂.obj.hom =
    tripleFst B W₁ W₂ W₃ ≫ pullback.fst W₁.obj.hom W₂.obj.hom ≫ W₁.obj.hom
  rw [← Category.assoc, ← tripleFst_snd, Category.assoc, ← pullback.condition]

/-- The projection of a triple overlap to the overlap of the outer two members. -/
public abbrev tripleFstThd :
    (smallEtaleTripleObj B W₁ W₂ W₃).obj.left ⟶ (smallEtaleOverlapObj B W₁ W₃).obj.left :=
  pullback.lift (tripleFst B W₁ W₂ W₃ ≫ pullback.fst W₁.obj.hom W₂.obj.hom)
    (tripleSnd B W₁ W₂ W₃ ≫ pullback.snd W₂.obj.hom W₃.obj.hom) (by
      have h := tripleSnd_hom B W₁ W₂ W₃
      change tripleSnd B W₁ W₂ W₃ ≫ pullback.fst W₂.obj.hom W₃.obj.hom ≫ W₂.obj.hom =
        tripleFst B W₁ W₂ W₃ ≫ pullback.fst W₁.obj.hom W₂.obj.hom ≫ W₁.obj.hom at h
      rw [Category.assoc, Category.assoc, ← h, pullback.condition])

/-- The outer projection of a triple overlap is a morphism over `S`. -/
public theorem tripleFstThd_hom :
    tripleFstThd B W₁ W₂ W₃ ≫ (smallEtaleOverlapObj B W₁ W₃).obj.hom =
      (smallEtaleTripleObj B W₁ W₂ W₃).obj.hom := by
  show tripleFstThd B W₁ W₂ W₃ ≫ pullback.fst W₁.obj.hom W₃.obj.hom ≫ W₁.obj.hom = _
  rw [← Category.assoc, pullback.lift_fst, Category.assoc]
  rfl

/-- The outer projection of a triple overlap, followed by the first projection. -/
public theorem tripleFstThd_fst :
    tripleFstThd B W₁ W₂ W₃ ≫ pullback.fst W₁.obj.hom W₃.obj.hom =
      tripleFst B W₁ W₂ W₃ ≫ pullback.fst W₁.obj.hom W₂.obj.hom :=
  pullback.lift_fst _ _ _

/-- The outer projection of a triple overlap, followed by the second projection. -/
public theorem tripleFstThd_snd :
    tripleFstThd B W₁ W₂ W₃ ≫ pullback.snd W₁.obj.hom W₃.obj.hom =
      tripleSnd B W₁ W₂ W₃ ≫ pullback.snd W₂.obj.hom W₃.obj.hom :=
  pullback.lift_snd _ _ _

/-- The second projection of an overlap is a morphism over `S`. -/
public theorem overlapSnd_hom :
    pullback.snd W₁.obj.hom W₂.obj.hom ≫ W₂.obj.hom = (smallEtaleOverlapObj B W₁ W₂).obj.hom :=
  pullback.condition.symm

variable {T : B.Scheme} (f : T ⟶ S)

/-- The first projection of an overlap, after base change. -/
public abbrev overlapFstBC :
    pullback (smallEtaleOverlapObj B W₁ W₂).obj.hom f ⟶ pullback W₁.obj.hom f :=
  smallEtaleBaseChangeMap B f (pullback.fst W₁.obj.hom W₂.obj.hom) rfl

/-- The second projection of an overlap, after base change. -/
public abbrev overlapSndBC :
    pullback (smallEtaleOverlapObj B W₁ W₂).obj.hom f ⟶ pullback W₂.obj.hom f :=
  smallEtaleBaseChangeMap B f (pullback.snd W₁.obj.hom W₂.obj.hom) (overlapSnd_hom B W₁ W₂)

/-- The first projection of a triple overlap, after base change. -/
public abbrev tripleFstBC :
    pullback (smallEtaleTripleObj B W₁ W₂ W₃).obj.hom f ⟶
      pullback (smallEtaleOverlapObj B W₁ W₂).obj.hom f :=
  smallEtaleBaseChangeMap B f (tripleFst B W₁ W₂ W₃) (tripleFst_hom B W₁ W₂ W₃)

/-- The second projection of a triple overlap, after base change. -/
public abbrev tripleSndBC :
    pullback (smallEtaleTripleObj B W₁ W₂ W₃).obj.hom f ⟶
      pullback (smallEtaleOverlapObj B W₂ W₃).obj.hom f :=
  smallEtaleBaseChangeMap B f (tripleSnd B W₁ W₂ W₃) (tripleSnd_hom B W₁ W₂ W₃)

/-- The outer projection of a triple overlap, after base change. -/
public abbrev tripleFstThdBC :
    pullback (smallEtaleTripleObj B W₁ W₂ W₃).obj.hom f ⟶
      pullback (smallEtaleOverlapObj B W₁ W₃).obj.hom f :=
  smallEtaleBaseChangeMap B f (tripleFstThd B W₁ W₂ W₃) (tripleFstThd_hom B W₁ W₂ W₃)

/-- **The base change of an overlap is the overlap of the base changes.** -/
public theorem isPullback_overlapBC :
    IsPullback (overlapFstBC B W₁ W₂ f) (overlapSndBC B W₁ W₂ f) (pullback.snd W₁.obj.hom f)
      (pullback.snd W₂.obj.hom f) :=
  isPullback_smallEtaleBaseChangeMap_of_isPullback B f _ _ _ _
    (IsPullback.of_hasPullback W₁.obj.hom W₂.obj.hom)

/-- **The base change of a triple overlap is the fibre product of the base changes of the two
overlaps over the base change of the middle member.** -/
public theorem isPullback_tripleBC :
    IsPullback (tripleFstBC B W₁ W₂ W₃ f) (tripleSndBC B W₁ W₂ W₃ f) (overlapSndBC B W₁ W₂ f)
      (overlapFstBC B W₂ W₃ f) :=
  isPullback_smallEtaleBaseChangeMap_of_isPullback' B f _ _ _ _ _ _ _ _
    (IsPullback.of_hasPullback (pullback.snd W₁.obj.hom W₂.obj.hom)
      (pullback.fst W₂.obj.hom W₃.obj.hom))

/-- The outer projection of a triple overlap, followed by the first projection, after base
change. -/
public theorem tripleFstThdBC_fst :
    tripleFstThdBC B W₁ W₂ W₃ f ≫ overlapFstBC B W₁ W₃ f =
      tripleFstBC B W₁ W₂ W₃ f ≫ overlapFstBC B W₁ W₂ f :=
  smallEtaleBaseChangeMap_comp_eq B f _ _ _ _ _ _ _ _ (tripleFstThd_fst B W₁ W₂ W₃)

/-- The outer projection of a triple overlap, followed by the second projection, after base
change. -/
public theorem tripleFstThdBC_snd :
    tripleFstThdBC B W₁ W₂ W₃ f ≫ overlapSndBC B W₁ W₃ f =
      tripleSndBC B W₁ W₂ W₃ f ≫ overlapSndBC B W₂ W₃ f :=
  smallEtaleBaseChangeMap_comp_eq B f _ _ _ _ _ _ _ _ (tripleFstThd_snd B W₁ W₂ W₃)

/-- The two maps of a triple overlap to the middle member agree after base change. -/
public theorem tripleFstBC_snd :
    tripleFstBC B W₁ W₂ W₃ f ≫ overlapSndBC B W₁ W₂ f =
      tripleSndBC B W₁ W₂ W₃ f ≫ overlapFstBC B W₂ W₃ f :=
  smallEtaleBaseChangeMap_comp_eq B f _ _ _ _ _ _ _ _ (tripleFst_snd B W₁ W₂ W₃)

end Triple

section MemberSquares

variable (B : BigEtaleSite.{u}) {I : Type u} [Preorder I]
  (Dg : Iᵒᵖ ⥤ B.Scheme) (c : Cone (Dg ⋙ B.inclusion)) (hX : B.Contains c.pt) (j : I)

/-- The projections of member cones commute with base change maps. -/
public theorem coneStageHom_memberCone_smallEtaleBaseChangeMap
    {Z Z' : SmallEtale B (Dg.obj (op j)).obj (Dg.obj (op j)).property}
    (φ : Z.obj.left ⟶ Z'.obj.left) (hφ : φ ≫ Z'.obj.hom = Z.obj.hom) (J : {J : I // j ≤ J}) :
    coneStageHom B (memberSystem B Dg j Z) (memberCone B Dg c hX j Z)
        (memberCone_contains B Dg c hX j Z) J ≫
        smallEtaleBaseChangeMap B (systemStageHom B Dg J.2) φ hφ =
      smallEtaleBaseChangeMap B (coneStageHom B Dg c hX j) φ hφ ≫
        coneStageHom B (memberSystem B Dg j Z') (memberCone B Dg c hX j Z')
          (memberCone_contains B Dg c hX j Z') J :=
  memberBaseChangeMap_smallEtaleBaseChangeMap B _ _ _ (coneStageHom_comp B Dg c hX J.2) φ hφ

/-- The transition morphisms of member systems commute with base change maps. -/
public theorem systemStageHom_memberSystem_smallEtaleBaseChangeMap
    {Z Z' : SmallEtale B (Dg.obj (op j)).obj (Dg.obj (op j)).property}
    (φ : Z.obj.left ⟶ Z'.obj.left) (hφ : φ ≫ Z'.obj.hom = Z.obj.hom) {J J' : {J : I // j ≤ J}}
    (h : J ≤ J') :
    systemStageHom B (memberSystem B Dg j Z) h ≫
        smallEtaleBaseChangeMap B (systemStageHom B Dg J.2) φ hφ =
      smallEtaleBaseChangeMap B (systemStageHom B Dg J'.2) φ hφ ≫
        systemStageHom B (memberSystem B Dg j Z') h :=
  memberBaseChangeMap_smallEtaleBaseChangeMap B _ _ _ (systemStageHom_comp B Dg _ _) φ hφ

end MemberSquares

section Descent

variable (B : BigEtaleSite.{u}) {A : Type t} [Category.{v} A]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous A
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (S : B.Scheme), HasWeakSheafify (SmallEtale.topology B S.obj S.property) A]
  {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (Dg : Iᵒᵖ ⥤ B.Scheme) (c : Cone (Dg ⋙ B.inclusion)) (hX : B.Contains c.pt)

/-- **Transitions of constant sheaves satisfying the cocycle condition descend to a stage.** Let
`{W_n}` be a finite family of affine objects of the small étale site of a stage `X_j`, and let
`σ n m` be isomorphisms between constant sheaves with values satisfying `P` over the base changes
`(W_n ×_{X_j} W_m) ×_{X_j} X` of the overlaps, satisfying the cocycle condition over the base
changes of the triple overlaps. Then at some stage `J ≥ j` there are isomorphisms `τ n m` over
`(W_n ×_{X_j} W_m) ×_{X_j} X_J` satisfying the cocycle condition there and transporting to the
`σ n m`.

The overlaps are the vertices of their member systems, so each `σ n m` comes from a stage
(`AlgebraicGeometry.exists_stage_transport_iso`), and the cocycle condition, which holds at the
vertex of the member system of each triple overlap, holds at a later stage
(`AlgebraicGeometry.exists_stage_transport_eq_of_transport_eq`). -/
public theorem exists_stage_transitions (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj)
    (P : A → Prop) (hloc : SmallEtaleConstantMapsLocallyConstant B A P)
    (hinj : SmallEtaleConstantFaithful B A) [HasLimitsOfSize.{u + 1, u + 1} A]
    (j : I) {K : Type (u + 1)} [Finite K]
    (W : K → SmallEtale B (Dg.obj (op j)).obj (Dg.obj (op j)).property)
    (hWaff : ∀ n, IsAffine (W n).obj.left.obj) (E : K → A) (hE : ∀ n, P (E n))
    (σ : ∀ n m, (constantSheaf (SmallEtale.topology B
        (pullback (smallEtaleOverlapObj B (W n) (W m)).obj.hom (coneStageHom B Dg c hX j)).obj
        (pullback (smallEtaleOverlapObj B (W n) (W m)).obj.hom
          (coneStageHom B Dg c hX j)).property) A).obj (E n) ≅
      (constantSheaf (SmallEtale.topology B
        (pullback (smallEtaleOverlapObj B (W n) (W m)).obj.hom (coneStageHom B Dg c hX j)).obj
        (pullback (smallEtaleOverlapObj B (W n) (W m)).obj.hom
          (coneStageHom B Dg c hX j)).property) A).obj (E m))
    (hσ : ∀ n m l,
      smallEtaleConstantTransport B A
          (tripleFstBC B (W n) (W m) (W l) (coneStageHom B Dg c hX j)) (σ n m).hom ≫
        smallEtaleConstantTransport B A
          (tripleSndBC B (W n) (W m) (W l) (coneStageHom B Dg c hX j)) (σ m l).hom =
      smallEtaleConstantTransport B A
          (tripleFstThdBC B (W n) (W m) (W l) (coneStageHom B Dg c hX j)) (σ n l).hom) :
    ∃ (J : I) (hjJ : j ≤ J) (τ : ∀ n m, (constantSheaf (SmallEtale.topology B
        (pullback (smallEtaleOverlapObj B (W n) (W m)).obj.hom (systemStageHom B Dg hjJ)).obj
        (pullback (smallEtaleOverlapObj B (W n) (W m)).obj.hom
          (systemStageHom B Dg hjJ)).property) A).obj (E n) ≅
      (constantSheaf (SmallEtale.topology B
        (pullback (smallEtaleOverlapObj B (W n) (W m)).obj.hom (systemStageHom B Dg hjJ)).obj
        (pullback (smallEtaleOverlapObj B (W n) (W m)).obj.hom
          (systemStageHom B Dg hjJ)).property) A).obj (E m)),
      (∀ n m l,
        smallEtaleConstantTransport B A
            (tripleFstBC B (W n) (W m) (W l) (systemStageHom B Dg hjJ)) (τ n m).hom ≫
          smallEtaleConstantTransport B A
            (tripleSndBC B (W n) (W m) (W l) (systemStageHom B Dg hjJ)) (τ m l).hom =
        smallEtaleConstantTransport B A
            (tripleFstThdBC B (W n) (W m) (W l) (systemStageHom B Dg hjJ)) (τ n l).hom) ∧
      ∀ n m, smallEtaleConstantTransport B A
          (memberConeHom B Dg c hX j (smallEtaleOverlapObj B (W n) (W m)) ⟨J, hjJ⟩)
          (τ n m).hom = (σ n m).hom := by
  classical
  have : QuasiSeparatedSpace (Dg.obj (op j)).obj := hqs j
  have hW2c : ∀ n m, CompactSpace (pullback (W n).obj.hom (W m).obj.hom).obj :=
    fun n m => by
      have := hWaff n
      have := hWaff m
      exact compactSpace_pullback_bigEtale B (W n).obj.hom (W m).obj.hom
  have hW2s : ∀ n m, QuasiSeparatedSpace (pullback (W n).obj.hom (W m).obj.hom).obj :=
    fun n m => by
      have := hWaff n
      have := hWaff m
      exact quasiSeparatedSpace_pullback_bigEtale B (W n).obj.hom (W m).obj.hom
  have hW3c : ∀ n m l,
      CompactSpace (smallEtaleTripleObj B (W n) (W m) (W l)).obj.left.obj := fun n m l => by
    have := hW2c n m
    have := hW2c m l
    have := hWaff m
    exact compactSpace_pullback_bigEtale B (pullback.snd (W n).obj.hom (W m).obj.hom)
      (pullback.fst (W m).obj.hom (W l).obj.hom)
  have hW3s : ∀ n m l,
      QuasiSeparatedSpace (smallEtaleTripleObj B (W n) (W m) (W l)).obj.left.obj :=
    fun n m l => by
      have := hW2s n m
      have := hW2s m l
      exact quasiSeparatedSpace_pullback_bigEtale B (pullback.snd (W n).obj.hom (W m).obj.hom)
        (pullback.fst (W m).obj.hom (W l).obj.hom)
  -- each transition comes from a stage
  have h1 := fun n m => exists_stage_transport_iso B
    (memberSystem B Dg j (smallEtaleOverlapObj B (W n) (W m)))
    (memberCone B Dg c hX j (smallEtaleOverlapObj B (W n) (W m)))
    (memberCone_contains B Dg c hX j _) (memberConeIsLimit B Dg c hX j _ hc)
    (memberSystem_isAffineHom haff) (memberSystem_compactSpace haff (hW2c n m))
    (memberSystem_quasiSeparatedSpace haff (hW2s n m)) P hloc hinj (hE n) (hE m) (σ n m)
    ⟨j, le_rfl⟩
  choose J₂ _ τ₂ hτ₂ using h1
  obtain ⟨J₀, hJ₀⟩ := Finite.exists_le (fun p : K × K => J₂ p.1 p.2)
  let τ₀ := fun n m => SmallEtaleGluing.constantTransport B A
    (systemStageHom B (memberSystem B Dg j (smallEtaleOverlapObj B (W n) (W m))) (hJ₀ (n, m)))
    (τ₂ n m)
  have hτ₀ : ∀ n m, smallEtaleConstantTransport B A
      (coneStageHom B (memberSystem B Dg j (smallEtaleOverlapObj B (W n) (W m)))
        (memberCone B Dg c hX j _) (memberCone_contains B Dg c hX j _) J₀) (τ₀ n m).hom =
      (σ n m).hom := fun n m =>
    (smallEtaleConstantTransport_coneStageHom_systemStageHom B _ _ _ (hJ₀ (n, m))
      (τ₂ n m).hom).trans (hτ₂ n m)
  -- the cocycle condition holds at a later stage
  have h3 : ∀ n m l, ∃ (J₃ : {J : I // j ≤ J}) (h : J₀ ≤ J₃),
      smallEtaleConstantTransport B A
          (systemStageHom B (memberSystem B Dg j (smallEtaleTripleObj B (W n) (W m) (W l))) h)
          (smallEtaleConstantTransport B A
              (tripleFstBC B (W n) (W m) (W l) (systemStageHom B Dg J₀.2)) (τ₀ n m).hom ≫
            smallEtaleConstantTransport B A
              (tripleSndBC B (W n) (W m) (W l) (systemStageHom B Dg J₀.2)) (τ₀ m l).hom) =
        smallEtaleConstantTransport B A
          (systemStageHom B (memberSystem B Dg j (smallEtaleTripleObj B (W n) (W m) (W l))) h)
          (smallEtaleConstantTransport B A
            (tripleFstThdBC B (W n) (W m) (W l) (systemStageHom B Dg J₀.2)) (τ₀ n l).hom) := by
    intro n m l
    refine exists_stage_transport_eq_of_transport_eq B
      (memberSystem B Dg j (smallEtaleTripleObj B (W n) (W m) (W l)))
      (memberCone B Dg c hX j _) (memberCone_contains B Dg c hX j _)
      (memberConeIsLimit B Dg c hX j _ hc) (memberSystem_isAffineHom haff)
      (memberSystem_compactSpace haff (hW3c n m l))
      (memberSystem_quasiSeparatedSpace haff (hW3s n m l)) P hloc hinj J₀ (hE n) _ _ ?_
    rw [smallEtaleConstantTransport_comp]
    iterate 3 rw [smallEtaleConstantTransport_square _ _ _ _
      (coneStageHom_memberCone_smallEtaleBaseChangeMap B Dg c hX j _ _ J₀), hτ₀]
    rw [hσ]
  choose J₃ hJ₃ hJ₃' using h3
  obtain ⟨J₁, hJ₁⟩ := Finite.exists_le
    (fun o : Option (K × K × K) => o.elim J₀ fun p => J₃ p.1 p.2.1 p.2.2)
  have hJ₀₁ : J₀ ≤ J₁ := hJ₁ none
  let τ₁ := fun n m => SmallEtaleGluing.constantTransport B A
    (systemStageHom B (memberSystem B Dg j (smallEtaleOverlapObj B (W n) (W m))) hJ₀₁)
    (τ₀ n m)
  refine ⟨J₁.1, J₁.2, τ₁, fun n m l => ?_, fun n m => ?_⟩
  · show smallEtaleConstantTransport B A _ (smallEtaleConstantTransport B A _ (τ₀ n m).hom) ≫
      smallEtaleConstantTransport B A _ (smallEtaleConstantTransport B A _ (τ₀ m l).hom) =
      smallEtaleConstantTransport B A _ (smallEtaleConstantTransport B A _ (τ₀ n l).hom)
    iterate 3 rw [smallEtaleConstantTransport_square _ _ _ _
      (systemStageHom_memberSystem_smallEtaleBaseChangeMap B Dg j _ _ hJ₀₁).symm]
    rw [← smallEtaleConstantTransport_comp]
    iterate 2 rw [← smallEtaleConstantTransport_systemStageHom_trans B _ (hJ₃ n m l)
      (hJ₁ (some (n, m, l)))]
    rw [hJ₃' n m l]
  · rw [← coneStageHom_memberCone]
    exact (smallEtaleConstantTransport_coneStageHom_systemStageHom B _ _ _ hJ₀₁
      (τ₀ n m).hom).trans (hτ₀ n m)

end Descent

section Iso

variable {C : Type*} [Category C]

/-- Two pairs of isomorphisms with the same transition. -/
public theorem isoTransition_hom_comp_inv_eq {X Y Cn Cm : C} (Dn : X ≅ Cn) (Dm : X ≅ Cm)
    (En : Y ≅ Cn) (Em : Y ≅ Cm) (h : Dn.inv ≫ Dm.hom = En.inv ≫ Em.hom) :
    Dn.hom ≫ En.inv = Dm.hom ≫ Em.inv := by
  have h' : Dm.hom = Dn.hom ≫ En.inv ≫ Em.hom := by rw [← h, Iso.hom_inv_id_assoc]
  rw [h', Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Cancellation in a chain of transitions. -/
public theorem isoTransition_cocycle {X Y Z W : C} (R₁ R₁' : X ≅ Y) (R₂ R₂' : X ≅ Z)
    (R₃ R₃' : X ≅ W) (e₁ : R₁ = R₁') (e₂ : R₂ = R₂') (e₃ : R₃ = R₃') :
    (R₁.inv ≫ R₂.hom) ≫ (R₂'.inv ≫ R₃.hom) = R₁'.inv ≫ R₃'.hom := by
  subst e₁ e₂ e₃
  simp

end Iso

section Comparison

variable {B : BigEtaleSite.{u}} {A : Type t} [Category.{v} A]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous A
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (S : B.Scheme), HasWeakSheafify (SmallEtale.topology B S.obj S.property) A]

/-- **Transport of a transition between restricted trivializations.** -/
public theorem smallEtaleConstantTransport_transition {S T₁ T₂ Y Y' : B.Scheme}
    {F : Sheaf (SmallEtale.topology B S.obj S.property) A} {s₁ : T₁ ⟶ S} {s₂ : T₂ ⟶ S}
    {E₁ E₂ : A}
    (ε₁ : (smallEtaleSheafPullback B A s₁).obj F ≅
      (constantSheaf (SmallEtale.topology B T₁.obj T₁.property) A).obj E₁)
    (ε₂ : (smallEtaleSheafPullback B A s₂).obj F ≅
      (constantSheaf (SmallEtale.topology B T₂.obj T₂.property) A).obj E₂)
    (a : Y ⟶ T₁) (b : Y ⟶ T₂) (r : Y ⟶ S) (ha : a ≫ s₁ = r) (hb : b ≫ s₂ = r)
    (g : Y' ⟶ Y) (r' : Y' ⟶ S) (hr : g ≫ r = r') :
    smallEtaleConstantTransport B A g
        ((smallEtaleTrivializationRestrict B A ε₁ a r ha).inv ≫
          (smallEtaleTrivializationRestrict B A ε₂ b r hb).hom) =
      (smallEtaleTrivializationRestrict B A ε₁ (g ≫ a) r'
          (by rw [Category.assoc, ha, hr])).inv ≫
        (smallEtaleTrivializationRestrict B A ε₂ (g ≫ b) r'
          (by rw [Category.assoc, hb, hr])).hom :=
  smallEtaleConstantTransport_restrict_inv_hom ε₁ ε₂ a b r ha hb g r' hr _ rfl _ rfl _ _

/-- The first projection of a fibre product along an étale morphism is étale. -/
public theorem etale_inclusion_map_pullback_snd {X Y Z : B.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z)
    [Etale (B.inclusion.map f)] : Etale (B.inclusion.map (pullback.snd f g)) :=
  MorphismProperty.of_isPullback ((IsPullback.of_hasPullback f g).map B.inclusion)
    ‹Etale (B.inclusion.map f)›

attribute [local instance] etale_inclusion_map_pullback_snd

/-- The base change of a covering, read through the second projections. -/
public theorem sieve_ofEtaleHom_pullback_snd {S T : B.Scheme} (f : T ⟶ S)
    {K : Type (u + 1)} (W : K → SmallEtale B S.obj S.property)
    (g : ∀ k, W k ⟶ SmallEtale.final B S.obj S.property)
    (hg : Sieve.ofArrows W g ∈ SmallEtale.topology B S.obj S.property
      (SmallEtale.final B S.obj S.property)) :
    Sieve.ofArrows (fun k => SmallEtale.ofEtaleHom B (pullback.snd (W k).obj.hom f))
      (fun _ => (SmallEtale.finalIsTerminal B T.obj T.property).from _) ∈
        SmallEtale.topology B T.obj T.property (SmallEtale.final B T.obj T.property) :=
  smallEtale_sieve_ofArrows_final_baseChange B f W g hg

variable [HasLimitsOfSize.{u + 1, u + 1} A]

omit [HasLimitsOfSize.{u + 1, u + 1} A] in
/-- **Two sheaves trivialized on a covering with the same transitions are isomorphic.** -/
public theorem nonempty_iso_of_trivializations {S : B.Scheme} {K : Type*}
    {X : K → B.Scheme} (f : ∀ k, X k ⟶ S) [∀ k, Etale (B.inclusion.map (f k))]
    (hf : Sieve.ofArrows (fun k => SmallEtale.ofEtaleHom B (f k))
      (fun _ => (SmallEtale.finalIsTerminal B S.obj S.property).from _) ∈
        SmallEtale.topology B S.obj S.property (SmallEtale.final B S.obj S.property))
    (O : K → K → B.Scheme) (a : ∀ k l, O k l ⟶ X k) (b : ∀ k l, O k l ⟶ X l)
    (r : ∀ k l, O k l ⟶ S) (hO : ∀ k l, IsPullback (a k l) (b k l) (f k) (f l))
    (hr₁ : ∀ k l, a k l ≫ f k = r k l) (hr₂ : ∀ k l, b k l ≫ f l = r k l)
    {F F' : Sheaf (SmallEtale.topology B S.obj S.property) A} (E : K → A)
    (ε : ∀ k, (smallEtaleSheafPullback B A (f k)).obj F ≅
      (constantSheaf (SmallEtale.topology B (X k).obj (X k).property) A).obj (E k))
    (δ : ∀ k, (smallEtaleSheafPullback B A (f k)).obj F' ≅
      (constantSheaf (SmallEtale.topology B (X k).obj (X k).property) A).obj (E k))
    (h : ∀ k l,
      (smallEtaleTrivializationRestrict B A (δ k) (a k l) (r k l) (hr₁ k l)).inv ≫
        (smallEtaleTrivializationRestrict B A (δ l) (b k l) (r k l) (hr₂ k l)).hom =
      (smallEtaleTrivializationRestrict B A (ε k) (a k l) (r k l) (hr₁ k l)).inv ≫
        (smallEtaleTrivializationRestrict B A (ε l) (b k l) (r k l) (hr₂ k l)).hom) :
    Nonempty (F' ≅ F) := by
  obtain ⟨ψ, hψ⟩ :=
    smallEtaleSheafPullback_exists_map_eq_of_isPullback B A S f hf O a b r hO hr₁ hr₂
    (fun k => (δ k).hom ≫ (ε k).inv) (fun k l => by
      rw [smallEtaleSheafPullbackCompIso'_conj_trivialization,
        smallEtaleSheafPullbackCompIso'_conj_trivialization]
      exact isoTransition_hom_comp_inv_eq _ _ _ _ (h k l))
  obtain ⟨ψ', hψ'⟩ :=
    smallEtaleSheafPullback_exists_map_eq_of_isPullback B A S f hf O a b r hO hr₁ hr₂
    (fun k => (ε k).hom ≫ (δ k).inv) (fun k l => by
      rw [smallEtaleSheafPullbackCompIso'_conj_trivialization,
        smallEtaleSheafPullbackCompIso'_conj_trivialization]
      exact isoTransition_hom_comp_inv_eq _ _ _ _ (h k l).symm)
  refine ⟨⟨ψ, ψ', ?_, ?_⟩⟩ <;>
  · refine smallEtaleSheafPullback_jointly_faithful B A S f hf _ _ fun k => ?_
    rw [Functor.map_comp, hψ, hψ', CategoryTheory.Functor.map_id]
    simp

/-- The transition between two restricted trivializations, written out. -/
public theorem smallEtaleTrivializationRestrict_inv_hom_eq_trans {S X₁ X₂ O : B.Scheme}
    {F : Sheaf (SmallEtale.topology B S.obj S.property) A} {f₁ : X₁ ⟶ S} {f₂ : X₂ ⟶ S}
    {E₁ E₂ : A}
    (ε₁ : (smallEtaleSheafPullback B A f₁).obj F ≅
      (constantSheaf (SmallEtale.topology B X₁.obj X₁.property) A).obj E₁)
    (ε₂ : (smallEtaleSheafPullback B A f₂).obj F ≅
      (constantSheaf (SmallEtale.topology B X₂.obj X₂.property) A).obj E₂)
    (p : O ⟶ X₁) (q : O ⟶ X₂) (r : O ⟶ S) (h₁ : p ≫ f₁ = r) (h₂ : q ≫ f₂ = r) :
    (smallEtaleTrivializationRestrict B A ε₁ p r h₁).inv ≫
        (smallEtaleTrivializationRestrict B A ε₂ q r h₂).hom =
      ((smallEtaleConstantPullbackIso B A p E₁).symm ≪≫
        (smallEtaleSheafPullback B A p).mapIso ε₁.symm ≪≫
        (smallEtaleSheafPullbackCompIso' B A p f₁ r h₁).app F ≪≫
        (smallEtaleSheafPullbackCompIso' B A q f₂ r h₂).symm.app F ≪≫
        (smallEtaleSheafPullback B A q).mapIso ε₂ ≪≫
        smallEtaleConstantPullbackIso B A q E₂).hom := by
  simp [smallEtaleTrivializationRestrict]

end Comparison

section Main

variable (B : BigEtaleSite.{u}) {A : Type t} [Category.{v} A]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous A
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (X : B.Scheme) (V : SmallEtale B X.obj X.property),
    HasWeakSheafify ((SmallEtale.topology B X.obj X.property).over V) A]
  [HasLimitsOfSize.{u + 1, u + 1} A]
  {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (Dg : Iᵒᵖ ⥤ B.Scheme) (c : Cone (Dg ⋙ B.inclusion)) (hX : B.Contains c.pt)

attribute [local instance] etale_inclusion_map_pullback_snd

/-- **Essential surjectivity for sheaves trivialized with values satisfying `P`.** Let `X` be
the limit of a directed inverse system of quasi-compact, quasi-separated schemes with affine
transition morphisms, and let the coefficient category be one in which morphisms of constant
sheaves with source satisfying `P` are locally constant and the constant sheaf functor is
faithful over nonempty schemes. Every sheaf on `X_étale` trivialized with values satisfying `P`
is the inverse image of a sheaf trivialized with values satisfying `P` at some stage.

The trivializing covering is refined by the base change of a finite affine covering `{W_n}` of a
stage; the transitions of `F` over the base changes of the overlaps descend, with their cocycle
condition, to a later stage (`AlgebraicGeometry.exists_stage_transitions`), where the constant
sheaves glue; the inverse image of the glued sheaf to `X` has the same trivializations and
transitions as `F`, hence is isomorphic to it
(`AlgebraicGeometry.nonempty_iso_of_trivializations`). -/
public theorem smallEtaleStagesEssSurj_isTrivialized (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj)
    (hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj)
    (P : A → Prop) (hloc : SmallEtaleConstantMapsLocallyConstant B A P)
    (hinj : SmallEtaleConstantFaithful B A) :
    SmallEtaleStagesEssSurj B A Dg c hX (IsTrivializedSmallEtaleSheaf B A P) := by
  classical
  intro F hF
  obtain ⟨K, V, g, hg, hV⟩ := hF (SmallEtale.final B c.pt hX)
  obtain ⟨j, -, K', hK', W, w, hW, hWaff, href⟩ :=
    smallEtaleStagesCoveringsRefine_affine_of_isLimit B Dg c hX hc haff hqc hqs
      (Classical.arbitrary I) K V g hg
  -- local trivializations of `F` over the base changes of the `W n`
  have triv : ∀ n, ∃ (E : A) (_ : P E), Nonempty
      ((smallEtaleSheafPullback B A (pullback.snd (W n).obj.hom (coneStageHom B Dg c hX j))).obj
          F ≅
        (constantSheaf (SmallEtale.topology B
          (pullback (W n).obj.hom (coneStageHom B Dg c hX j)).obj
          (pullback (W n).obj.hom (coneStageHom B Dg c hX j)).property) A).obj E) := by
    intro n
    obtain ⟨m, ⟨q⟩⟩ := href n
    obtain ⟨E, hE, ⟨e⟩⟩ := hV m
    obtain ⟨e'⟩ := (nonempty_constantSheafIso_over_iff B c.pt hX (V m) A F E).mp ⟨e⟩
    exact ⟨E, hE, ⟨smallEtaleTrivializationRestrict B A e'.symm q.hom.left _ (Over.w q.hom)⟩⟩
  choose E hE hε using triv
  let ε := fun n => (hε n).some
  -- the transitions over the overlaps of the base changes
  let θ := fun n m =>
    (smallEtaleTrivializationRestrict B A (ε n)
      (overlapFstBC B (W n) (W m) (coneStageHom B Dg c hX j))
      (pullback.snd (smallEtaleOverlapObj B (W n) (W m)).obj.hom (coneStageHom B Dg c hX j))
      (smallEtaleBaseChangeMap_snd B _ _ _)).symm ≪≫
    smallEtaleTrivializationRestrict B A (ε m)
      (overlapSndBC B (W n) (W m) (coneStageHom B Dg c hX j))
      (pullback.snd (smallEtaleOverlapObj B (W n) (W m)).obj.hom (coneStageHom B Dg c hX j))
      (smallEtaleBaseChangeMap_snd B _ _ _)
  have hθ : ∀ n m l,
      smallEtaleConstantTransport B A
          (tripleFstBC B (W n) (W m) (W l) (coneStageHom B Dg c hX j)) (θ n m).hom ≫
        smallEtaleConstantTransport B A
          (tripleSndBC B (W n) (W m) (W l) (coneStageHom B Dg c hX j)) (θ m l).hom =
      smallEtaleConstantTransport B A
          (tripleFstThdBC B (W n) (W m) (W l) (coneStageHom B Dg c hX j)) (θ n l).hom := by
    intro n m l
    let π := coneStageHom B Dg c hX j
    let r := pullback.snd (smallEtaleTripleObj B (W n) (W m) (W l)).obj.hom π
    simp only [θ, Iso.trans_hom, Iso.symm_hom]
    rw [smallEtaleConstantTransport_transition _ _ _ _ _ _ _ _ r
        (smallEtaleBaseChangeMap_snd B _ _ _),
      smallEtaleConstantTransport_transition _ _ _ _ _ _ _ _ r
        (smallEtaleBaseChangeMap_snd B _ _ _),
      smallEtaleConstantTransport_transition _ _ _ _ _ _ _ _ r
        (smallEtaleBaseChangeMap_snd B _ _ _)]
    exact isoTransition_cocycle _ _ _ _ _ _
      (smallEtaleTrivializationRestrict_congr _ _ _ _ (tripleFstThdBC_fst B _ _ _ π).symm)
      (smallEtaleTrivializationRestrict_congr _ _ _ _ (tripleFstBC_snd B _ _ _ π))
      (smallEtaleTrivializationRestrict_congr _ _ _ _ (tripleFstThdBC_snd B _ _ _ π).symm)
  -- the transitions descend to a stage
  obtain ⟨J, hjJ, τ, hτ, hτθ⟩ := exists_stage_transitions B Dg c hX hc haff hqs P hloc hinj j W
    hWaff E hE θ hθ
  let t := systemStageHom B Dg hjJ
  -- glue the constant sheaves at that stage
  obtain ⟨F₂, ε₂, hε₂⟩ := smallEtaleSheaf_exists_glue_constant_of_isPullback B A (Dg.obj (op J))
    (fun n => pullback.snd (W n).obj.hom t) (sieve_ofEtaleHom_pullback_snd t W w hW)
    (fun n m => pullback (smallEtaleOverlapObj B (W n) (W m)).obj.hom t)
    (fun n m => overlapFstBC B (W n) (W m) t) (fun n m => overlapSndBC B (W n) (W m) t)
    (fun n m => pullback.snd (smallEtaleOverlapObj B (W n) (W m)).obj.hom t)
    (fun n m => isPullback_overlapBC B (W n) (W m) t)
    (fun n m => smallEtaleBaseChangeMap_snd B _ _ _)
    (fun n m => smallEtaleBaseChangeMap_snd B _ _ _)
    (fun n m l => pullback (smallEtaleTripleObj B (W n) (W m) (W l)).obj.hom t)
    (fun n m l => tripleFstBC B (W n) (W m) (W l) t)
    (fun n m l => tripleSndBC B (W n) (W m) (W l) t)
    (fun n m l => tripleFstThdBC B (W n) (W m) (W l) t)
    (fun n m l => isPullback_tripleBC B (W n) (W m) (W l) t)
    (fun n m l => tripleFstBC B (W n) (W m) (W l) t ≫ overlapFstBC B (W n) (W m) t)
    (fun n m l => tripleFstBC B (W n) (W m) (W l) t ≫ overlapSndBC B (W n) (W m) t)
    (fun n m l => tripleSndBC B (W n) (W m) (W l) t ≫ overlapSndBC B (W m) (W l) t)
    (fun n m l => rfl) (fun n m l => rfl)
    (fun n m l => (tripleFstBC_snd B (W n) (W m) (W l) t).symm) (fun n m l => rfl)
    (fun n m l => tripleFstThdBC_fst B (W n) (W m) (W l) t)
    (fun n m l => tripleFstThdBC_snd B (W n) (W m) (W l) t) E τ
    (fun n m l => Iso.ext (by
      simpa only [smallEtaleConstantTransport, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
        Category.assoc] using hτ n m l))
  refine ⟨J, F₂, ?_, ?_⟩
  · intro U
    refine Stacks.ConstantSheaf.Localization.exists_trivializing_cover
      (SmallEtale.topology B (Dg.obj (op J)).obj (Dg.obj (op J)).property) A
      (SmallEtale.finalIsTerminal B (Dg.obj (op J)).obj (Dg.obj (op J)).property) F₂ P
      (X := fun n => SmallEtale.ofEtaleHom B (pullback.snd (W n).obj.hom t))
      (f := fun n => (SmallEtale.finalIsTerminal B (Dg.obj (op J)).obj
        (Dg.obj (op J)).property).from _) (sieve_ofEtaleHom_pullback_snd t W w hW)
      (fun n => ⟨E n, hE n, (nonempty_constantSheafIso_over_iff B _ _ _ A F₂ (E n)).mpr
        ⟨(ε₂ n).symm⟩⟩) U
  · let π := coneStageHom B Dg c hX j
    let πJ := coneStageHom B Dg c hX J
    let μ := fun n => memberConeHom B Dg c hX j (W n) ⟨J, hjJ⟩
    have hμ : ∀ n, μ n ≫ pullback.snd (W n).obj.hom t =
        pullback.snd (W n).obj.hom π ≫ πJ := fun n =>
      memberConeHom_snd B Dg c hX j (W n) ⟨J, hjJ⟩
    refine nonempty_iso_of_trivializations (fun n => pullback.snd (W n).obj.hom π)
      (sieve_ofEtaleHom_pullback_snd π W w hW)
      (fun n m => pullback (smallEtaleOverlapObj B (W n) (W m)).obj.hom π)
      (fun n m => overlapFstBC B (W n) (W m) π) (fun n m => overlapSndBC B (W n) (W m) π)
      (fun n m => pullback.snd (smallEtaleOverlapObj B (W n) (W m)).obj.hom π)
      (fun n m => isPullback_overlapBC B (W n) (W m) π)
      (fun n m => smallEtaleBaseChangeMap_snd B _ _ _)
      (fun n m => smallEtaleBaseChangeMap_snd B _ _ _) E ε
      (fun n => (smallEtaleSheafPullbackCompIso' B A (pullback.snd (W n).obj.hom π) πJ
        (pullback.snd (W n).obj.hom π ≫ πJ) rfl).app F₂ ≪≫
          smallEtaleTrivializationRestrict B A (ε₂ n) (μ n) _ (hμ n)) fun n m => ?_
    let ν := memberConeHom B Dg c hX j (smallEtaleOverlapObj B (W n) (W m)) ⟨J, hjJ⟩
    rw [smallEtaleTrivialization_transition_pullback πJ (ε₂ m) (ε₂ n) _ _ (μ m) (μ n)
      (hμ m) (hμ n) (overlapSndBC B (W n) (W m) π) (overlapFstBC B (W n) (W m) π) _ _ _
      (overlapSndBC B (W n) (W m) t) (overlapFstBC B (W n) (W m) t)
      (pullback.snd (smallEtaleOverlapObj B (W n) (W m)).obj.hom t)
      (smallEtaleBaseChangeMap_snd B _ _ _) (smallEtaleBaseChangeMap_snd B _ _ _) ν
      (coneStageHom_memberCone_smallEtaleBaseChangeMap B Dg c hX j _ _ ⟨J, hjJ⟩).symm
      (coneStageHom_memberCone_smallEtaleBaseChangeMap B Dg c hX j _ _ ⟨J, hjJ⟩).symm
      (memberConeHom_snd B Dg c hX j _ ⟨J, hjJ⟩)]
    have h2 := congrArg Iso.hom (hε₂ n m)
    have h3 : (smallEtaleTrivializationRestrict B A (ε₂ n) (overlapFstBC B (W n) (W m) t)
        (pullback.snd (smallEtaleOverlapObj B (W n) (W m)).obj.hom t)
        (smallEtaleBaseChangeMap_snd B _ _ _)).inv ≫
        (smallEtaleTrivializationRestrict B A (ε₂ m) (overlapSndBC B (W n) (W m) t)
          (pullback.snd (smallEtaleOverlapObj B (W n) (W m)).obj.hom t)
          (smallEtaleBaseChangeMap_snd B _ _ _)).hom = (τ n m).hom := by
      exact (smallEtaleTrivializationRestrict_inv_hom_eq_trans _ _ _ _ _ _ _).trans h2
    rw [h3]
    exact hτθ n m

end Main

section Mono

variable (B : BigEtaleSite.{u}) {A : Type t} [Category.{v} A]
  [∀ (X : B.Scheme) (V : SmallEtale B X.obj X.property),
    HasWeakSheafify ((SmallEtale.topology B X.obj X.property).over V) A]

/-- Trivializability is monotone in the property of the values. -/
public theorem isTrivializedSmallEtaleSheaf_mono {Q Q' : A → Prop} (h : ∀ E, Q E → Q' E)
    (X : B.Scheme) (F : Sheaf (SmallEtale.topology B X.obj X.property) A)
    (hF : IsTrivializedSmallEtaleSheaf B A Q X F) : IsTrivializedSmallEtaleSheaf B A Q' X F :=
  fun U => by
    obtain ⟨K, V, g, hg, hV⟩ := hF U
    exact ⟨K, V, g, hg, fun k => by
      obtain ⟨E, hE, e⟩ := hV k
      exact ⟨E, h E hE, e⟩⟩

end Mono

section Instances

attribute [local instance high] Stacks.ConstantSheaf.hasSheafify_moduleCat_of_univLE

attribute [local instance] SmallEtale.isRightAdjointPushforward_type
  SmallEtale.isRightAdjointPushforward_addCommGrpCat
  SmallEtale.isRightAdjointPushforward_moduleCat_site

variable (B : BigEtaleSite.{u}) {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (Dg : Iᵒᵖ ⥤ B.Scheme) (c : Cone (Dg ⋙ B.inclusion)) (hX : B.Contains c.pt)

/-- **Essential surjectivity, clause (1) of Tag 0GL2.** For `X = lim X_i` the limit of a directed
inverse system of quasi-compact, quasi-separated schemes with affine transition morphisms, every
finite locally constant sheaf of sets on `X_étale` is the inverse image of a finite locally
constant sheaf of sets at some stage. -/
public theorem smallEtaleStagesEssSurj_isFiniteLocallyConstant_type (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj)
    (hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj) :
    SmallEtaleStagesEssSurj B (Type (u + 1)) Dg c hX
      (isFiniteLocallyConstantSmallEtaleSheaf B (Type (u + 1))) := by
  intro F hF
  obtain ⟨i, Fi, hFi, e⟩ := smallEtaleStagesEssSurj_isTrivialized B Dg c hX hc haff hqc hqs
    (fun E => Finite E) (smallEtaleConstantMapsLocallyConstant_type B)
    (smallEtaleConstantFaithful_type B) F
    ((isTrivialized_iff_isFiniteLocallyConstant B (Type (u + 1)) (B.obj c.pt hX) F).mpr hF)
  exact ⟨i, Fi,
    (isTrivialized_iff_isFiniteLocallyConstant B (Type (u + 1)) (Dg.obj (op i)) Fi).mp hFi, e⟩

/-- **Essential surjectivity, clause (2) of Tag 0GL2.** For `X = lim X_i` as in clause (1), every
finite locally constant sheaf of abelian groups on `X_étale` is the inverse image of a finite
locally constant sheaf of abelian groups at some stage. -/
public theorem smallEtaleStagesEssSurj_isFiniteLocallyConstant_addCommGrpCat (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj)
    (hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj) :
    SmallEtaleStagesEssSurj B AddCommGrpCat.{u + 1} Dg c hX
      (isFiniteLocallyConstantSmallEtaleSheaf B AddCommGrpCat.{u + 1}) := by
  intro F hF
  obtain ⟨i, Fi, hFi, e⟩ := smallEtaleStagesEssSurj_isTrivialized B Dg c hX hc haff hqc hqs
    (fun E : AddCommGrpCat.{u + 1} => Finite E)
    (smallEtaleConstantMapsLocallyConstant_addCommGrpCat B)
    (smallEtaleConstantFaithful_addCommGrpCat B) F
    ((isTrivialized_iff_isFiniteLocallyConstant B AddCommGrpCat.{u + 1} (B.obj c.pt hX)
      F).mpr hF)
  exact ⟨i, Fi,
    (isTrivialized_iff_isFiniteLocallyConstant B AddCommGrpCat.{u + 1} (Dg.obj (op i))
      Fi).mp hFi, e⟩

/-- **Essential surjectivity, clause (3) of Tag 0GL2.** For `X = lim X_i` as in clause (1) and any
commutative ring `Λ`, every locally constant sheaf of `Λ`-modules of finite type on `X_étale` is
the inverse image of a locally constant sheaf of `Λ`-modules of finite type at some stage. No
Noetherian hypothesis on `Λ` is needed. -/
public theorem smallEtaleStagesEssSurj_isFiniteTypeLocallyConstant_moduleCat
    (Λ : Type (u + 1)) [CommRing Λ] (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj)
    (hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj) :
    SmallEtaleStagesEssSurj B (ModuleCat.{u + 1} Λ) Dg c hX
      (isFiniteTypeLocallyConstantSmallEtaleSheaf.{u + 1} B Λ) := by
  intro F hF
  obtain ⟨i, Fi, hFi, e⟩ := smallEtaleStagesEssSurj_isTrivialized B Dg c hX hc haff hqc hqs
    (fun E : ModuleCat.{u + 1} Λ => Module.Finite Λ E)
    (smallEtaleConstantMapsLocallyConstant_moduleCat B Λ)
    (smallEtaleConstantFaithful_moduleCat B Λ) F
    (isTrivializedSmallEtaleSheaf_mono B (Q := fun E : ModuleCat.{u + 1} Λ => ModuleCat.isFG Λ E)
      (fun E hE => (ModuleCat.isFG_iff E).mp hE) (B.obj c.pt hX) F hF)
  exact ⟨i, Fi, isTrivializedSmallEtaleSheaf_mono B
    (Q' := fun E : ModuleCat.{u + 1} Λ => ModuleCat.isFG Λ E)
    (fun E hE => (ModuleCat.isFG_iff E).mpr hE) (Dg.obj (op i)) Fi hFi, e⟩

end Instances

end AlgebraicGeometry

end
