module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitFormalTowerRing

/-!
# Functoriality of the ring `lim_n Γ(X ×_V Spec (A / I^{n+1}), 𝒪)`

For a commutative square of a morphism `h : X' ⟶ X` of algebraic spaces over a morphism
`v : V' ⟶ V` of affine Noetherian objects of the site, with ideals `I ⊆ Γ(V, 𝒪)` and
`I' ⊆ Γ(V', 𝒪)` such that `I Γ(V', 𝒪) ⊆ I'`, the fibres `X' ×_{V'} Spec (A' / I'^n)` map to the
fibres `X ×_V Spec (A / I^n)`, and restriction of functions along these maps is a ring map
`lim_n Γ(X ×_V Spec (A / I^{n+1}), 𝒪) ⟶ lim_n Γ(X' ×_{V'} Spec (A' / I'^{n+1}), 𝒪)`.

## Main definitions

* `AlgebraicGeometry.Artin.FormalRing.fibreMap`: the morphism of fibres over `h`.
* `AlgebraicGeometry.Artin.FormalRing.towerRingMap`: the ring map of tower rings.

## Main results

* `AlgebraicGeometry.Artin.FormalRing.towerRingMap_id`, `towerRingMap_comp`: functoriality.
* `AlgebraicGeometry.Artin.FormalRing.towerRingMap_comp_towerRingHom`: the ring map of the
  restriction of a morphism `X_{/g⁻¹ V(I)} ⟶ Spf B` to `X'` is the image of its ring map.
* `AlgebraicGeometry.Artin.FormalRing.towerRingMap_comp_alpha`: `α` is natural.
* `AlgebraicGeometry.Artin.FormalRing.towerRingMap_mem_towerFiltration`: the filtrations are
  preserved.

## References

* [Stacks Project, Tag 0GI5](https://stacks.math.columbia.edu/tag/0GI5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Topology

universe u

namespace AlgebraicGeometry.Artin.FormalRing

open Space FormalSpace FormalDictionary

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance]
  AlgebraicGeometry.Artin.FormalDictionary.instTopologicalSpaceAdicCompletion

/-- **Restriction of functions along the identity is the identity.** -/
theorem globalSectionsRingHomSite_id (X : AlgebraicSpaces B S hS) :
    globalSectionsRingHomSite B S hS (𝟙 X) = RingHom.id _ := by
  refine RingHom.ext fun a => Subtype.ext (funext fun U => ?_)
  let d : ChartDiagram B S hS X.1 X.1 (𝟙 X : X ⟶ X).hom :=
    ⟨U.unop, U.unop, 𝟙 _, by
      show U.unop.1.hom ≫ 𝟙 _ = yoneda.map (𝟙 _) ≫ U.unop.1.hom
      rw [Category.comp_id, CategoryTheory.Functor.map_id, Category.id_comp]⟩
  refine (globalSectionsRingHomSite_val_chartDiagram B S hS (𝟙 X) a d).trans ?_
  show (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (𝟙 _)).op).hom (a.1 (op U.unop)) =
    a.1 U
  rw [CategoryTheory.Functor.map_id, op_id, CategoryTheory.Functor.map_id]
  rfl

/-- A ring map sending `I` into `J` sends `I ^ n` into `J ^ n`. -/
private theorem map_pow_le_pow {R R' : Type*} [CommRing R] [CommRing R'] (f : R →+* R')
    {I : Ideal R} {J : Ideal R'} (hIJ : I.map f ≤ J) (n : ℕ) : (I ^ n).map f ≤ J ^ n :=
  (Ideal.map_pow f I n).trans_le (Ideal.pow_right_mono hIJ n)

section Map

variable {V V' : BigFppfOver B S hS} (v : V' ⟶ V)
  {I : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)}
  {I' : Ideal Γ((BigFppfOver.toScheme B S hS).obj V', ⊤)}
  (hII : I.map ((BigFppfOver.toScheme B S hS).map v).appTop.hom ≤ I')

include hII in
/-- The morphism `Spec (A' / I'^n) ⟶ Spec (A / I^n)` over `v`. -/
theorem exists_adicQuotientObj_map [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V')] (n : ℕ) :
    ∃ t : adicCompletionQuotientObj B S hS V' I' n ⟶ adicCompletionQuotientObj B S hS V I n,
      t ≫ adicCompletionQuotientObjHom B S hS V I n =
        adicCompletionQuotientObjHom B S hS V' I' n ≫ v := by
  refine (exists_comp_adicCompletionQuotientObjHom_iff (V := V) (K := I) _ n).2 ?_
  intro a ha
  rw [RingHom.mem_ker, Functor.map_comp, Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
    RingHom.comp_apply]
  have h1 : ((BigFppfOver.toScheme B S hS).map v).appTop.hom a ∈ I' ^ n :=
    map_pow_le_pow _ hII n (Ideal.mem_map_of_mem _ ha)
  rwa [← ker_appTop_adicCompletionQuotientObjHom (V := V') (K := I') n] at h1

variable [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj V')]
  {X X' : AlgebraicSpaces B S hS} (g : X.1 ⟶ yoneda.obj V) (g' : X'.1 ⟶ yoneda.obj V')
  (h : X'.1 ⟶ X.1) (hsq : h ≫ g = g' ≫ yoneda.map v)

include hII hsq in
/-- The composite `X' ×_{V'} Spec (A' / I'^n) ⟶ X' ⟶ X` lands in the thickening
`X ×_V Spec (A / I^n)`. -/
theorem range_fibreInclusion_comp_le (n : ℕ) :
    Subfunctor.range ((fibreInclusion V' I' (spaceHom V' g') n).hom ≫ h) ≤
      (fibreThickening V I (spaceHom V g) n).1 := by
  rintro T _ ⟨y, rfl⟩
  obtain ⟨z, hz⟩ := y.2
  obtain ⟨t, ht⟩ := exists_adicQuotientObj_map v hII n
  refine ⟨z ≫ t, ?_⟩
  have hz' : z ≫ adicCompletionQuotientObjHom B S hS V' I' n = g'.app T y.1 := hz
  show z ≫ t ≫ adicCompletionQuotientObjHom B S hS V I n = g.app T (h.app T y.1)
  refine (congrArg (z ≫ ·) ht).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ v) hz').trans ?_
  exact (congrArg (fun m => m.app T y.1) hsq).symm

/-- **The morphism of fibres** `X' ×_{V'} Spec (A' / I'^n) ⟶ X ×_V Spec (A / I^n)` over `h`. -/
def fibreMap (n : ℕ) :
    fibreSpace V' I' (spaceHom V' g') n ⟶ fibreSpace V I (spaceHom V g) n :=
  ObjectProperty.homMk (Subfunctor.lift (G := (fibreThickening V I (spaceHom V g) n).1)
    ((fibreInclusion V' I' (spaceHom V' g') n).hom ≫ h)
    (range_fibreInclusion_comp_le v hII g g' h hsq n))

/-- The morphism of fibres followed by the inclusion of the fibre into `X` is the inclusion of
the fibre into `X'` followed by `h`. -/
theorem fibreMap_comp (n : ℕ) :
    (fibreMap v hII g g' h hsq n).hom ≫ (fibreInclusion V I (spaceHom V g) n).hom =
      (fibreInclusion V' I' (spaceHom V' g') n).hom ≫ h :=
  rfl

/-- The morphism of fibres commutes with the inclusions of the thickenings into `X'` and `X`. -/
theorem fibreMap_hom_ι (n : ℕ) :
    (fibreMap v hII g g' h hsq n).hom ≫ (fibreThickening V I (spaceHom V g) n).1.ι =
      (fibreThickening V' I' (spaceHom V' g') n).1.ι ≫ h :=
  rfl

/-- Two morphisms into the fibre `X ×_V Spec (A / I^n)` agree if they agree after inclusion
into `X`. -/
theorem fibreMap_ext {n : ℕ} {Y : AlgebraicSpaces B S hS}
    {m₁ m₂ : Y ⟶ fibreSpace V I (spaceHom V g) n}
    (e : m₁.hom ≫ (fibreThickening V I (spaceHom V g) n).1.ι =
      m₂.hom ≫ (fibreThickening V I (spaceHom V g) n).1.ι) : m₁ = m₂ :=
  ObjectProperty.hom_ext _ ((cancel_mono _).1 e)

/-- The morphisms of fibres commute with the transition maps between fibres. -/
theorem fibreTransition_comp_fibreMap {m n : ℕ} (hmn : m ≤ n) :
    fibreTransition V' I' (spaceHom V' g') hmn ≫ fibreMap v hII g g' h hsq n =
      fibreMap v hII g g' h hsq m ≫ fibreTransition V I (spaceHom V g) hmn := by
  refine fibreMap_ext g ?_
  rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
    Category.assoc, Category.assoc, fibreMap_hom_ι]
  show Subfunctor.homOfLe (fibreThickening_le V' I' (spaceHom V' g') hmn) ≫ _ ≫ h =
    _ ≫ Subfunctor.homOfLe (fibreThickening_le V I (spaceHom V g) hmn) ≫ _
  rw [Subfunctor.homOfLe_ι_assoc, Subfunctor.homOfLe_ι, fibreMap_hom_ι]

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj V')] in
/-- The `n + 1`-st component of an element of the tower ring restricts to its `n`-th component
along the transition map of fibres. -/
theorem towerRing_transition (n : ℕ) :
    (globalSectionsRingHomSite B S hS
        (fibreTransition V I (spaceHom V g) (Nat.le_succ (n + 1)))).comp
        ((Pi.evalRingHom (fun m => FibreRing (I := I) g m) (n + 1)).comp (towerRing I g).subtype) =
      (Pi.evalRingHom (fun m => FibreRing (I := I) g m) n).comp (towerRing I g).subtype :=
  RingHom.ext fun x => x.2 n

/-- Restriction of functions along the morphisms of fibres commutes with restriction along the
transition maps. -/
theorem globalSectionsRingHomSite_fibreMap_transition (n : ℕ) :
    (globalSectionsRingHomSite B S hS
        (fibreTransition V' I' (spaceHom V' g') (Nat.le_succ (n + 1)))).comp
        (globalSectionsRingHomSite B S hS (fibreMap v hII g g' h hsq (n + 1 + 1))) =
      (globalSectionsRingHomSite B S hS (fibreMap v hII g g' h hsq (n + 1))).comp
        (globalSectionsRingHomSite B S hS
          (fibreTransition V I (spaceHom V g) (Nat.le_succ (n + 1)))) := by
  rw [← globalSectionsRingHomSite_comp, ← globalSectionsRingHomSite_comp,
    fibreTransition_comp_fibreMap]

/-- **The ring map of restriction along the morphisms of fibres**,
`lim_n Γ(X ×_V Spec (A / I^{n+1}), 𝒪) ⟶ lim_n Γ(X' ×_{V'} Spec (A' / I'^{n+1}), 𝒪)`. -/
def towerRingMap : towerRing I g →+* towerRing I' g' :=
  towerLift g' (fun n => (globalSectionsRingHomSite B S hS
      (fibreMap v hII g g' h hsq (n + 1))).comp ((Pi.evalRingHom _ n).comp (towerRing I g).subtype))
    (fun n => by
      rw [← RingHom.comp_assoc, globalSectionsRingHomSite_fibreMap_transition, RingHom.comp_assoc,
        towerRing_transition])

/-- The `n`-th component of the image of `x` under the tower ring map is the restriction of the
`n`-th component of `x` along the morphism of fibres. -/
theorem towerRingMap_apply (x : towerRing I g) (n : ℕ) :
    (towerRingMap v hII g g' h hsq x).1 n =
      globalSectionsRingHomSite B S hS (fibreMap v hII g g' h hsq (n + 1)) (x.1 n) :=
  rfl

/-- **The tower ring map preserves the filtrations.** -/
theorem towerRingMap_mem_towerFiltration {x : towerRing I g} {n : ℕ}
    (hx : x ∈ towerFiltration I g n) : towerRingMap v hII g g' h hsq x ∈ towerFiltration I' g' n :=
  fun m hm => by rw [towerRingMap_apply, hx m hm, map_zero]

end Map

section Functoriality

variable {V : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
  {I : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)}
  {X : AlgebraicSpaces B S hS} (g : X.1 ⟶ yoneda.obj V)

/-- **The tower ring map of the identity is the identity.** -/
theorem towerRingMap_id (v : V ⟶ V)
    (hII : I.map ((BigFppfOver.toScheme B S hS).map v).appTop.hom ≤ I) (h : X.1 ⟶ X.1)
    (hsq : h ≫ g = g ≫ yoneda.map v) (hh : h = 𝟙 _) :
    towerRingMap v hII g g h hsq = RingHom.id _ := by
  refine RingHom.ext fun x => Subtype.ext (funext fun n => ?_)
  have e : fibreMap v hII g g h hsq (n + 1) = 𝟙 _ := by
    refine fibreMap_ext g ?_
    rw [fibreMap_hom_ι, hh, Category.comp_id, ObjectProperty.FullSubcategory.id_hom,
      Category.id_comp]
  rw [towerRingMap_apply, e, globalSectionsRingHomSite_id]
  rfl

variable {V' V'' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj V')]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj V'')]
  {I' : Ideal Γ((BigFppfOver.toScheme B S hS).obj V', ⊤)}
  {I'' : Ideal Γ((BigFppfOver.toScheme B S hS).obj V'', ⊤)}
  {X' X'' : AlgebraicSpaces B S hS} (g' : X'.1 ⟶ yoneda.obj V') (g'' : X''.1 ⟶ yoneda.obj V'')

/-- **The tower ring maps compose.** -/
theorem towerRingMap_comp (v : V' ⟶ V) (v' : V'' ⟶ V') (v'' : V'' ⟶ V)
    (hII : I.map ((BigFppfOver.toScheme B S hS).map v).appTop.hom ≤ I')
    (hII' : I'.map ((BigFppfOver.toScheme B S hS).map v').appTop.hom ≤ I'')
    (hII'' : I.map ((BigFppfOver.toScheme B S hS).map v'').appTop.hom ≤ I'')
    (h : X'.1 ⟶ X.1) (h' : X''.1 ⟶ X'.1) (h'' : X''.1 ⟶ X.1)
    (hsq : h ≫ g = g' ≫ yoneda.map v) (hsq' : h' ≫ g' = g'' ≫ yoneda.map v')
    (hsq'' : h'' ≫ g = g'' ≫ yoneda.map v'') (hh : h' ≫ h = h'') :
    (towerRingMap v' hII' g' g'' h' hsq').comp (towerRingMap v hII g g' h hsq) =
      towerRingMap v'' hII'' g g'' h'' hsq'' := by
  refine RingHom.ext fun x => Subtype.ext (funext fun n => ?_)
  have e : fibreMap v' hII' g' g'' h' hsq' (n + 1) ≫ fibreMap v hII g g' h hsq (n + 1) =
      fibreMap v'' hII'' g g'' h'' hsq'' (n + 1) := by
    refine fibreMap_ext g ?_
    rw [ObjectProperty.FullSubcategory.comp_hom, Category.assoc, fibreMap_hom_ι,
      ← Category.assoc, fibreMap_hom_ι, Category.assoc, hh, fibreMap_hom_ι]
  rw [RingHom.comp_apply, towerRingMap_apply, towerRingMap_apply, towerRingMap_apply,
    ← RingHom.comp_apply, ← globalSectionsRingHomSite_comp, e]

end Functoriality

/-- Restricting along `k` the pullback of a function on `V` along `f` is the pullback along `t`
of its restriction along `p`, when `k ≫ f` is `t ≫ p`. -/
private theorem globalSectionsRingHomSite_pullbackRingHom_of_comp_eq {V W : BigFppfOver B S hS}
    {X X' : AlgebraicSpaces B S hS} (k : X' ⟶ X) (f : X ⟶ schemeSpace V)
    (t : X'.1 ⟶ yoneda.obj W) (p : W ⟶ V)
    (hk : k.hom ≫ f.hom = t ≫ yoneda.map p)
    (a : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) :
    globalSectionsRingHomSite B S hS k (pullbackRingHom B V f a) =
      pullbackRingHom B W (ObjectProperty.homMk t)
        (((BigFppfOver.toScheme B S hS).map p).appTop.hom a) :=
  (congrArg (fun φ => φ a) (globalSectionsRingHomSite_comp_pullbackRingHom (V := V) k f)).trans
    ((congrArg (fun m => pullbackRingHom B V m a)
      (ObjectProperty.hom_ext _ hk : k ≫ f = ObjectProperty.homMk (t ≫ yoneda.map p))).trans
      (pullbackRingHom_homMk_comp X' t p a))

section Naturality

variable {V : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
  [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)]
  {I : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)}

variable (I) in
/-- `Spec (A^∧ ⧸ I^{n+1} A^∧) ⟶ V` on functions is `A ⟶ A^∧ ⟶ A^∧ ⧸ I^{n+1} A^∧`. -/
theorem appTop_powStageToV (n : ℕ) (a : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) :
    ((BigFppfOver.toScheme B S hS).map (powStageToV V I n)).appTop.hom a =
      powStageRingHom' I n
        (algebraMap _ (AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) a) := by
  have e₁ : ((BigFppfOver.toScheme B S hS).map (powStageToV V I n)).appTop.hom a =
      ((BigFppfOver.toScheme B S hS).map (powStageToAffine V I n)).appTop.hom
        (((BigFppfOver.toScheme B S hS).map (affineModelHom V)).appTop.hom a) := by
    rw [powStageToV, Functor.map_comp, Scheme.Hom.comp_appTop]
    rfl
  have e₂ : ((BigFppfOver.toScheme B S hS).map (affineModelHom V)).appTop.hom a =
      (Scheme.ΓSpecIso (CommRingCat.of Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))).inv.hom a := by
    have hiso : ((BigFppfOver.toScheme B S hS).obj V).isoSpec.inv.appTop =
        (Scheme.ΓSpecIso Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)).inv := by
      rw [← cancel_mono (Scheme.ΓSpecIso Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)).hom,
        Iso.inv_hom_id, ← Scheme.toSpecΓ_appTop, ← Scheme.isoSpec_hom, ← Scheme.Hom.comp_appTop,
        Iso.hom_inv_id]
      rfl
    rw [toScheme_map_affineModelHom, hiso]
    rfl
  rw [e₁, e₂]
  exact (congrArg (fun φ => φ.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom
    ((Ideal.Quotient.mk
      (FormalSpace.adicCompletionPowStageIdeal I I.fg_of_isNoetherianRing n).1).comp
      (algebraMap Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
        (AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))))))).symm

variable {X : AlgebraicSpaces B S hS} (g : X.1 ⟶ yoneda.obj V)

variable (I) in
/-- **The component of `α` on the image of `A`** is the restriction to the fibre of the pullback
of functions. -/
theorem alphaComp_algebraMap (n : ℕ) (a : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) :
    alphaComp I g n (algebraMap _ (AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) a) =
      globalSectionsRingHomSite B S hS (fibreInclusion V I (spaceHom V g) (n + 1))
        (pullbackRingHom B V (spaceHom V g) a) := by
  have e₁ : alphaComp I g n
      (algebraMap _ (AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) a) =
      pullbackRingHom B (powStage V I n) (ObjectProperty.homMk (fibreToPowStage V I g n))
        (((BigFppfOver.toScheme B S hS).map (powStageToV V I n)).appTop.hom a) := by
    rw [appTop_powStageToV]
    rfl
  exact e₁.trans (globalSectionsRingHomSite_pullbackRingHom_of_comp_eq _ _ _ _
    (fibreToPowStage_comp V I g n).symm a).symm

variable (I) in
/-- **The restriction of functions to the fibres**,
`Γ(X, 𝒪) ⟶ lim_n Γ(X ×_V Spec (A / I^{n+1}), 𝒪)`. -/
def towerOf : ↥(Stacks.Cohomology.SiteModules.GlobalSectionRing
      (Stacks.SheafOfModules.Tensor.ringSheaf (Space.smallEtaleRingedSite B S hS X.1 X.2).O)) →+*
    towerRing I g :=
  towerLift g
    (fun n => globalSectionsRingHomSite B S hS (fibreInclusion V I (spaceHom V g) (n + 1)))
    (fun n => by rw [← globalSectionsRingHomSite_comp, fibreTransition_comp])

omit [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)] in
/-- The `n`-th component of `towerOf I g c` is the restriction of `c` to the fibre
`X ×_V Spec (A / I^{n+1})`. -/
theorem towerOf_apply (c : ↥(Stacks.Cohomology.SiteModules.GlobalSectionRing
      (Stacks.SheafOfModules.Tensor.ringSheaf (Space.smallEtaleRingedSite B S hS X.1 X.2).O)))
    (n : ℕ) :
    (towerOf I g c).1 n =
      globalSectionsRingHomSite B S hS (fibreInclusion V I (spaceHom V g) (n + 1)) c :=
  rfl

variable {Z : Set (Space.points B S hS (yoneda.obj V))}
  (hZI : ∀ x, x ∈ Z ↔ Space.pointsToScheme B S hS V x ∈
    ((BigFppfOver.toScheme B S hS).obj V).zeroLocus
      (I : Set Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)))
  (hqc : ∀ n, IsQuasiCompactSpace B S hS (fibreSpace V I (spaceHom V g) n).1)

/-- **`α` on the image of `A`** is the restriction of the pullback of functions. -/
theorem alpha_algebraMap (a : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) :
    alpha g hZI hqc (algebraMap _ (AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) a) =
      towerOf I g (pullbackRingHom B V (spaceHom V g) a) :=
  Subtype.ext (funext fun n => alphaComp_algebraMap I g n a)

/-- The `n`-th component of `α` vanishes on `I^{n+1} A^∧`. -/
theorem alphaComp_eq_zero {n : ℕ} {y : AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)}
    (hy : y ∈ (I ^ (n + 1)).map
      (algebraMap _ (AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)))) :
    alphaComp I g n y = 0 := by
  show pullbackRingHom B _ _ (powStageRingHom' I n y) = 0
  rw [powStageRingHom'_eq_zero hy, map_zero]

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] in
/-- The map of adic completions induced by `f : A →+* A'` sends the image of `a` to the image
of `f a`. -/
theorem completionRingHom_algebraMap {A A' : Type u} [CommRing A] [CommRing A'] (f : A →+* A')
    {J : Ideal A} {J' : Ideal A'} (hJ : J.map f ≤ J') (a : A) :
    completionRingHom f hJ (algebraMap A (AdicCompletion J A) a) =
      algebraMap A' (AdicCompletion J' A') (f a) := by
  rw [AdicCompletion.algebraMap_apply, AdicCompletion.algebraMap_apply, completionRingHom_of]
  rfl

variable {V' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj V')]
  [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj V', ⊤)] (v : V' ⟶ V)
  {I' : Ideal Γ((BigFppfOver.toScheme B S hS).obj V', ⊤)}
  (hII : I.map ((BigFppfOver.toScheme B S hS).map v).appTop.hom ≤ I')
  {X' : AlgebraicSpaces B S hS} (g' : X'.1 ⟶ yoneda.obj V')
  (h : X'.1 ⟶ X.1) (hsq : h ≫ g = g' ≫ yoneda.map v)

omit [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)]
  [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj V', ⊤)] in
/-- The morphism of fibres followed by the inclusion of the fibre into `X` is the inclusion of
the fibre into `X'` followed by `h`, as morphisms of algebraic spaces. -/
theorem fibreMap_comp_fibreInclusion (n : ℕ) :
    fibreMap v hII g g' h hsq n ≫ fibreInclusion V I (spaceHom V g) n =
      fibreInclusion V' I' (spaceHom V' g') n ≫ (ObjectProperty.homMk h : X' ⟶ X) :=
  ObjectProperty.hom_ext _ (by
    rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom]
    exact fibreMap_comp v hII g g' h hsq n)

omit [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)]
  [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj V', ⊤)] in
/-- **Restriction to the fibres is natural.** -/
theorem towerRingMap_comp_towerOf :
    (towerRingMap v hII g g' h hsq).comp (towerOf I g) =
      (towerOf I' g').comp
        (globalSectionsRingHomSite B S hS (ObjectProperty.homMk h : X' ⟶ X)) := by
  refine RingHom.ext fun c => Subtype.ext (funext fun n => ?_)
  rw [RingHom.comp_apply, RingHom.comp_apply, towerRingMap_apply, towerOf_apply, towerOf_apply,
    ← RingHom.comp_apply, ← globalSectionsRingHomSite_comp, fibreMap_comp_fibreInclusion,
    globalSectionsRingHomSite_comp, RingHom.comp_apply]

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
  [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj V')]
  [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj V', ⊤)] in
include hsq in
/-- Restricting along `h` the pullback to `X` of a function on `V` is the pullback to `X'` of
its restriction along `v`. -/
theorem globalSectionsRingHomSite_pullbackRingHom (a : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) :
    globalSectionsRingHomSite B S hS (ObjectProperty.homMk h : X' ⟶ X)
        (pullbackRingHom B V (spaceHom V g) a) =
      pullbackRingHom B V' (spaceHom V' g')
        (((BigFppfOver.toScheme B S hS).map v).appTop.hom a) := by
  exact globalSectionsRingHomSite_pullbackRingHom_of_comp_eq _ _ _ _
    hsq a

variable {Z' : Set (Space.points B S hS (yoneda.obj V'))}
  (hZI' : ∀ x, x ∈ Z' ↔ Space.pointsToScheme B S hS V' x ∈
    ((BigFppfOver.toScheme B S hS).obj V').zeroLocus
      (I' : Set Γ((BigFppfOver.toScheme B S hS).obj V', ⊤)))
  (hqc' : ∀ n, IsQuasiCompactSpace B S hS (fibreSpace V' I' (spaceHom V' g') n).1)

include hsq in
/-- **The components of `α` are natural.** -/
theorem globalSectionsRingHomSite_fibreMap_comp_alphaComp (n : ℕ) :
    (globalSectionsRingHomSite B S hS (fibreMap v hII g g' h hsq (n + 1))).comp (alphaComp I g n) =
      (alphaComp I' g' n).comp
        (completionRingHom ((BigFppfOver.toScheme B S hS).map v).appTop.hom hII) := by
  refine RingHom.ext fun x => ?_
  obtain ⟨a, ha⟩ := Ideal.exists_sub_algebraMap_mem_map_pow I x (n + 1)
  have hx : x = algebraMap _ _ a + (x - algebraMap _ _ a) := (add_sub_cancel _ _).symm
  have hy : completionRingHom ((BigFppfOver.toScheme B S hS).map v).appTop.hom hII
      (x - algebraMap _ _ a) ∈ (I' ^ (n + 1)).map (algebraMap _ _) := by
    have hle : ((I ^ (n + 1)).map (algebraMap _ (AdicCompletion I
        Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)))).map
          (completionRingHom ((BigFppfOver.toScheme B S hS).map v).appTop.hom hII) ≤
        (I' ^ (n + 1)).map (algebraMap _ _) := by
      rw [Ideal.map_map, Ideal.map_le_iff_le_comap]
      intro b hb
      rw [Ideal.mem_comap, RingHom.comp_apply, completionRingHom_algebraMap]
      exact Ideal.mem_map_of_mem _ (map_pow_le_pow _ hII (n + 1) (Ideal.mem_map_of_mem _ hb))
    exact hle (Ideal.mem_map_of_mem _ ha)
  rw [RingHom.comp_apply, RingHom.comp_apply]
  have z₇ := congrArg (fun φ => φ (pullbackRingHom B V (spaceHom V g) a))
    (globalSectionsRingHomSite_comp B S hS (fibreMap v hII g g' h hsq (n + 1))
      (fibreInclusion V I (spaceHom V g) (n + 1)))
  have z₈ := congrArg (fun φ => φ (pullbackRingHom B V (spaceHom V g) a))
    (globalSectionsRingHomSite_comp B S hS (fibreInclusion V' I' (spaceHom V' g') (n + 1))
      (ObjectProperty.homMk h : X' ⟶ X))
  have z₉ := congrArg
    (fun m => globalSectionsRingHomSite B S hS m (pullbackRingHom B V (spaceHom V g) a))
    (fibreMap_comp_fibreInclusion g v hII g' h hsq (n + 1))
  calc globalSectionsRingHomSite B S hS (fibreMap v hII g g' h hsq (n + 1)) (alphaComp I g n x)
      = globalSectionsRingHomSite B S hS (fibreMap v hII g g' h hsq (n + 1))
          (alphaComp I g n (algebraMap _ _ a) + alphaComp I g n (x - algebraMap _ _ a)) :=
        congrArg _ ((congrArg (alphaComp I g n) hx).trans (map_add (alphaComp I g n) _ _))
    _ = globalSectionsRingHomSite B S hS (fibreMap v hII g g' h hsq (n + 1))
          (alphaComp I g n (algebraMap _ _ a)) :=
        congrArg _ ((congrArg (_ + ·) (alphaComp_eq_zero g ha)).trans (add_zero _))
    _ = globalSectionsRingHomSite B S hS (fibreMap v hII g g' h hsq (n + 1))
          (globalSectionsRingHomSite B S hS (fibreInclusion V I (spaceHom V g) (n + 1))
            (pullbackRingHom B V (spaceHom V g) a)) := congrArg _ (alphaComp_algebraMap I g n a)
    _ = globalSectionsRingHomSite B S hS (fibreInclusion V' I' (spaceHom V' g') (n + 1))
          (globalSectionsRingHomSite B S hS (ObjectProperty.homMk h : X' ⟶ X)
            (pullbackRingHom B V (spaceHom V g) a)) := z₇.symm.trans (z₉.trans z₈)
    _ = globalSectionsRingHomSite B S hS (fibreInclusion V' I' (spaceHom V' g') (n + 1))
          (pullbackRingHom B V' (spaceHom V' g')
            (((BigFppfOver.toScheme B S hS).map v).appTop.hom a)) :=
        congrArg _ (globalSectionsRingHomSite_pullbackRingHom g v g' h hsq a)
    _ = alphaComp I' g' n (completionRingHom ((BigFppfOver.toScheme B S hS).map v).appTop.hom hII
          (algebraMap _ _ a)) :=
        (alphaComp_algebraMap I' g' n
          (((BigFppfOver.toScheme B S hS).map v).appTop.hom a)).symm.trans
          (congrArg _ (completionRingHom_algebraMap _ hII a).symm)
    _ = alphaComp I' g' n (completionRingHom ((BigFppfOver.toScheme B S hS).map v).appTop.hom hII
          (algebraMap _ _ a)) + alphaComp I' g' n (completionRingHom
            ((BigFppfOver.toScheme B S hS).map v).appTop.hom hII (x - algebraMap _ _ a)) :=
        ((congrArg (_ + ·) (alphaComp_eq_zero g' hy)).trans (add_zero _)).symm
    _ = alphaComp I' g' n
          (completionRingHom ((BigFppfOver.toScheme B S hS).map v).appTop.hom hII x) :=
        (map_add (alphaComp I' g' n) _ _).symm.trans (congrArg (alphaComp I' g' n)
          ((map_add (completionRingHom ((BigFppfOver.toScheme B S hS).map v).appTop.hom hII)
            _ _).symm.trans
            (congrArg _ hx.symm)))

include hZI hqc hZI' hqc' in
/-- **`α` is natural.** -/
theorem towerRingMap_comp_alpha :
    (towerRingMap v hII g g' h hsq).comp (alpha g hZI hqc) =
      (alpha g' hZI' hqc').comp
        (completionRingHom ((BigFppfOver.toScheme B S hS).map v).appTop.hom hII) := by
  refine RingHom.ext fun x => Subtype.ext (funext fun n => ?_)
  rw [RingHom.comp_apply, towerRingMap_apply, RingHom.comp_apply]
  exact DFunLike.congr_fun
    (globalSectionsRingHomSite_fibreMap_comp_alphaComp g v hII g' h hsq n) x

variable {Bt : Type u} [CommRing Bt] [TopologicalSpace Bt] [IsTopologicalRing Bt]
  [IsLinearTopology Bt Bt] (hB : TopologicalRing.IsWeaklyAdmissible Bt)
  {DB : QuotientSystem B S hS Bt}

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
  [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)] in
include hZI' hsq in
/-- If `Z'` maps into `Z`, then the points of the fibre `X' ×_{V'} Spec (A' / I'^{n+1})` map
into the preimage of `Z` in `X`. -/
theorem pointsMap_fibreInclusion_comp_mem (hZ : Z' ⊆ pointsMap B S hS _ (yoneda.map v) ⁻¹' Z)
    (n : ℕ) (x : Space.points B S hS (fibreSpace V' I' (spaceHom V' g') (n + 1)).1) :
    pointsMap B S hS _ ((fibreInclusion V' I' (spaceHom V' g') (n + 1)).hom ≫ h) x ∈
      pointsMap B S hS X.1 g ⁻¹' Z := by
  show pointsMap B S hS _ g (pointsMap B S hS _ _ x) ∈ Z
  rw [← Space.pointsMap_comp_apply, Category.assoc, hsq, ← Category.assoc,
    Space.pointsMap_comp_apply, Space.pointsMap_comp_apply]
  exact hZ (pointsMap_fibreInclusion_mem g' hZI' n x)

include hZI hZI' in
/-- **The ring maps of the fibres of a restriction.** -/
theorem fibreRingHom_completionSheafRestrict
    (hZ : Z' ⊆ pointsMap B S hS _ (yoneda.map v) ⁻¹' Z)
    (hsub : pointsMap B S hS X'.1 g' ⁻¹' Z' ⊆
      pointsMap B S hS X'.1 h ⁻¹' (pointsMap B S hS X.1 g ⁻¹' Z))
    (F : completionSheaf B S hS X.1 (pointsMap B S hS X.1 g ⁻¹' Z) ⟶ formalSpectrum DB) (n : ℕ) :
    fibreRingHom g' hZI' hB hqc' (completionSheafRestrict B S hS h _ _ hsub ≫ F) n =
      (globalSectionsRingHomSite B S hS (fibreMap v hII g g' h hsq (n + 1))).comp
        (fibreRingHom g hZI hB hqc F n) := by
  have h₁ := pointsMap_fibreInclusion_comp_mem g v g' h hsq hZI' hZ n
  have h₂ : ∀ x, pointsMap B S hS _ ((fibreMap v hII g g' h hsq (n + 1)).hom ≫
      (fibreInclusion V I (spaceHom V g) (n + 1)).hom) x ∈ pointsMap B S hS X.1 g ⁻¹' Z := by
    rwa [fibreMap_comp]
  have hm : toCompletion (fibreInclusion V' I' (spaceHom V' g') (n + 1)).hom _
        (pointsMap_fibreInclusion_mem g' hZI' n) ≫ completionSheafRestrict B S hS h _ _ hsub ≫ F =
      sheafifiedULiftMap B S hS (fibreMap v hII g g' h hsq (n + 1)).hom ≫
        toCompletion (fibreInclusion V I (spaceHom V g) (n + 1)).hom _
          (pointsMap_fibreInclusion_mem g hZI n) ≫ F := by
    rw [← Category.assoc, toCompletion_comp_completionSheafRestrict (h' := h₁),
      toCompletion_congr (fibreMap_comp v hII g g' h hsq (n + 1)).symm _ h₁ h₂,
      toCompletion_comp_left (h := pointsMap_fibreInclusion_mem g hZI n), Category.assoc]
  exact (congrArg (formalRingHom hB (fibreSpace V' I' (spaceHom V' g') (n + 1)) (hqc' (n + 1)))
    hm).trans (formalRingHom_comp hB (fibreSpace V I (spaceHom V g) (n + 1))
      (fibreMap v hII g g' h hsq (n + 1)) (hqc' (n + 1)) (hqc (n + 1)) _)

include hZI hZI' in
/-- **The ring map of a restriction** of `F : X_{/g⁻¹ V(I)} ⟶ Spf B` to `X'` is the image of
`ψ_F` under the tower ring map. -/
theorem towerRingMap_comp_towerRingHom
    (hZ : Z' ⊆ pointsMap B S hS _ (yoneda.map v) ⁻¹' Z)
    (hsub : pointsMap B S hS X'.1 g' ⁻¹' Z' ⊆
      pointsMap B S hS X'.1 h ⁻¹' (pointsMap B S hS X.1 g ⁻¹' Z))
    (F : completionSheaf B S hS X.1 (pointsMap B S hS X.1 g ⁻¹' Z) ⟶ formalSpectrum DB) :
    (towerRingMap v hII g g' h hsq).comp (towerRingHom g hZI hqc hB F) =
      towerRingHom g' hZI' hqc' hB (completionSheafRestrict B S hS h _ _ hsub ≫ F) := by
  refine RingHom.ext fun b => Subtype.ext (funext fun n => ?_)
  rw [RingHom.comp_apply, towerRingMap_apply]
  exact (congrArg (fun φ => φ b) (fibreRingHom_completionSheafRestrict g hZI hqc v hII g' h hsq
    hZI' hqc' hB hZ hsub F n)).symm

end Naturality

end AlgebraicGeometry.Artin.FormalRing

end
