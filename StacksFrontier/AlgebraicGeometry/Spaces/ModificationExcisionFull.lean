module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedEtaleDiagonalComplementRange
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationExcisionFaithful

/-!
# Fullness of the base-change functor on modifications

Let `f : V ⟶ W` be a separated étale morphism of algebraic spaces over a scheme `S` and let
`T` be a closed subspace of `W` whose preimage is carried isomorphically onto `T` by `f`.
Write `W⁰` for the open complement of `T`. This file proves that the base-change functor of
Stacks 0BGY is full.

## Main definitions

* `AlgebraicGeometry.Space.overComplementHom` is the canonical comparison, over the open
  complement, between two morphisms to `W` which are isomorphisms there.

## Main results

* `AlgebraicGeometry.Space.eq_of_app_eq_of_mem`: a morphism restricting to an isomorphism from
  the preimage of a subfunctor onto it separates sections lying over that subfunctor.
* `AlgebraicGeometry.Space.eq_of_locally_eq`: two sections of a sheaf agreeing along a covering
  sieve are equal.
* `AlgebraicGeometry.Space.full_baseChangeFunctor_of_diagonalComplement`: fullness of the
  base-change functor, given the decomposition `V ×_W V = Δ(V) ⨿ U` of the source proof in the
  form of a subfunctor `C` playing the role of `U`.
* `AlgebraicGeometry.Space.full_baseChangeFunctor`: **Stacks 0BGY**, fullness of the
  base-change functor, with the decomposition discharged.
* `AlgebraicGeometry.Space.fullyFaithful_baseChangeFunctor`: **Stacks 0BGY**, the base-change
  functor is fully faithful.

## Implementation notes

Fullness is the glueing half of the sheaf condition, run on the covering of
`AlgebraicGeometry.Space.excisionBaseMap`: the part of `X` lying over `W⁰`, and the fibre
product `X ×_W V`. On the first member the morphism is forced, since both `X` and `X'` are
isomorphisms over `W⁰`; on the second it is the given morphism, read through the first
projection. `CategoryTheory.Subfunctor.fromPreimage` being invertible is what makes the first
of these available, and `AlgebraicGeometry.Space.eq_of_app_eq_of_mem` is the elementwise
consequence used throughout.

The compatibility condition of `AlgebraicGeometry.Space.glueHom` has four cases, of which
three are immediate. The fourth — two sections of `X ×_W V` with the same image in `X`, that
is one section of `X` with two different lifts of its base point to `V` — is where the source
proof's decomposition `V ×_W V = Δ(V) ⨿ U` enters, and it is the only place separatedness of
`f` is used. The pair of lifts is a section of `V ×_W V`; locally it lies either in the range
of the diagonal, where the two lifts coincide, or in `C`, where its base point lies in `W⁰`
and the two values are separated by the previous paragraph. Since the source of a modification
is an fppf sheaf, local agreement is agreement.

The decomposition is proved first with the hypotheses `hC` and `hcov` left standing, and then
discharged by
`AlgebraicGeometry.Space.exists_subfunctor_sheafify_sup_range_diagonal_eq_top`:
`AlgebraicGeometry.Space.exists_diagonalComplement_decomposition` supplies it only at the
level of point sets, and what is needed is the subfunctor-level statement — that a *section*
lying in the diagonal piece has equal projections, which equality of point sets does not
give.

## References

* [Stacks Project, Tag 0BGY](https://stacks.math.columbia.edu/tag/0BGY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Separation over a subfunctor -/

/-- A morphism which restricts to an isomorphism from the preimage of a subfunctor onto that
subfunctor separates the sections lying over it: two sections with the same image, that image
lying in the subfunctor, are equal. -/
theorem eq_of_app_eq_of_mem {F W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : F ⟶ W)
    (W₀ : Subfunctor W) (hiso : IsIso (W₀.fromPreimage g)) {A : (BigFppfOver B S hS)ᵒᵖ}
    {x₁ x₂ : F.obj A} (hx : g.app A x₁ = g.app A x₂) (h₁ : g.app A x₁ ∈ W₀.obj A) :
    x₁ = x₂ := by
  have h₂ : g.app A x₂ ∈ W₀.obj A := hx ▸ h₁
  have key : ∀ a : (W₀.preimage g).toFunctor.obj A,
      (inv (W₀.fromPreimage g)).app A ((W₀.fromPreimage g).app A a) = a := by
    intro a
    have hid := ConcreteCategory.congr_hom
      (NatTrans.congr_app (IsIso.hom_inv_id (W₀.fromPreimage g)) A) a
    simpa only [NatTrans.comp_app, ConcreteCategory.comp_apply, types_comp_apply,
      NatTrans.id_app, types_id_apply] using hid
  have heq : (W₀.fromPreimage g).app A ⟨x₁, h₁⟩ = (W₀.fromPreimage g).app A ⟨x₂, h₂⟩ :=
    Subtype.ext hx
  have hsub : (⟨x₁, h₁⟩ : (W₀.preimage g).toFunctor.obj A) = ⟨x₂, h₂⟩ :=
    (key ⟨x₁, h₁⟩).symm.trans
      ((congrArg ((inv (W₀.fromPreimage g)).app A) heq).trans (key ⟨x₂, h₂⟩))
  exact congrArg Subtype.val hsub

/-- Two sections of a sheaf which agree after restriction along every arrow of a covering
sieve are equal. -/
theorem eq_of_locally_eq {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hP : Presheaf.IsSheaf (BigFppfOver.topology B S hS) P) {Z : BigFppfOver B S hS}
    {a b : P.obj (op Z)} (R : Sieve Z) (hR : R ∈ BigFppfOver.topology B S hS Z)
    (h : ∀ ⦃Y : BigFppfOver B S hS⦄ ⦃k : Y ⟶ Z⦄, R k → P.map k.op a = P.map k.op b) :
    a = b :=
  (((isSheaf_iff_isSheaf_of_type _ P).1 hP) R hR).isSeparatedFor.ext h

/-! ### The canonical comparison over the open complement -/

variable {F F' W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- For two morphisms to `W` which are isomorphisms over the subfunctor `W₀`, the canonical
morphism from the part of the source of the first lying over `W₀` to the source of the
second. -/
noncomputable def overComplementHom (W₀ : Subfunctor W) (g : F ⟶ W) (g' : F' ⟶ W)
    (hiso : IsIso (W₀.fromPreimage g')) : (W₀.preimage g).toFunctor ⟶ F' :=
  have := hiso
  W₀.fromPreimage g ≫ inv (W₀.fromPreimage g') ≫ (W₀.preimage g').ι

/-- The canonical comparison lies over `W`. -/
theorem overComplementHom_comp (W₀ : Subfunctor W) (g : F ⟶ W) (g' : F' ⟶ W)
    (hiso : IsIso (W₀.fromPreimage g')) :
    overComplementHom B S hS W₀ g g' hiso ≫ g' = (W₀.preimage g).ι ≫ g := by
  have := hiso
  rw [overComplementHom, Category.assoc, Category.assoc, ← W₀.fromPreimage_ι g',
    IsIso.inv_hom_id_assoc, W₀.fromPreimage_ι g]

/-! ### Fullness -/

variable {V W' : AlgebraicSpaces B S hS}

/-- **Stacks 0BGY, fullness of the base-change functor**, given the decomposition
`V ×_W V = Δ(V) ⨿ U` of the source proof: `C` is the complementary piece `U`, `hC` says that
its two projections land over the open complement of `T` (the step `U ×_W T = ∅`), and `hcov`
says that `C` and the diagonal cover the fibre square locally.

Every morphism of modifications after base change along `f` comes from a morphism of
modifications of `W`. -/
theorem full_baseChangeFunctor_of_diagonalComplement (f : V ⟶ W') (T : Subfunctor W'.obj)
    (hT : IsClosedSubspace B S hS T) (hfT : IsIso (T.fromPreimage f.hom))
    (hf : IsEtale B S hS f.hom)
    (C : Subfunctor (pullback f.hom f.hom))
    (hC : C ≤ (openComplement B S hS T).preimage (pullback.fst f.hom f.hom ≫ f.hom))
    (hcov : (C ⊔ Subfunctor.range (pullback.diagonal f.hom)).sheafify
      (BigFppfOver.topology B S hS) = ⊤) :
    (baseChangeFunctor B S hS f (openComplement B S hS T)).1.Full := by
  classical
  set J := BigFppfOver.topology B S hS with hJdef
  set W₀ := openComplement B S hS T with hW₀def
  constructor
  intro X X' β
  set g := X.obj.hom with hgdef
  set g' := X'.obj.hom with hg'def
  have hisoX : IsIso (W₀.fromPreimage g) :=
    isIso_fromPreimage_of_isIso_pullback_snd g W₀ X.property.2
  have hisoX' : IsIso (W₀.fromPreimage g') :=
    isIso_fromPreimage_of_isIso_pullback_snd g' W₀ X'.property.2
  -- Read the given morphism as a morphism of the fibre products, with that syntactic type.
  obtain ⟨βleft, hβleft⟩ :
      ∃ b : pullback g f.hom ⟶ pullback g' f.hom, b = β.hom.left := ⟨β.hom.left, rfl⟩
  have hβw : βleft ≫ pullback.snd g' f.hom = pullback.snd g f.hom := by
    rw [hβleft]; exact Over.w β.hom
  -- The two members of the glueing family.
  set φtrue := overComplementHom B S hS W₀ g g' hisoX' with hφtrue
  set φfalse := βleft ≫ pullback.fst g' f.hom with hφfalse
  -- Both lie over `W`, with the same composite as the corresponding projection.
  have htrue_w : φtrue ≫ g' = (W₀.preimage g).ι ≫ g :=
    overComplementHom_comp B S hS W₀ g g' hisoX'
  have hfalse_w : φfalse ≫ g' = pullback.fst g f.hom ≫ g :=
    calc φfalse ≫ g' = βleft ≫ pullback.fst g' f.hom ≫ g' := by
          rw [hφfalse]; exact Category.assoc _ _ _
      _ = βleft ≫ pullback.snd g' f.hom ≫ f.hom := by rw [pullback.condition]
      _ = (βleft ≫ pullback.snd g' f.hom) ≫ f.hom := (Category.assoc _ _ _).symm
      _ = pullback.snd g f.hom ≫ f.hom := by rw [hβw]
      _ = pullback.fst g f.hom ≫ g := pullback.condition.symm
  -- The elementwise forms.
  have htrue_app : ∀ (A : (BigFppfOver B S hS)ᵒᵖ) (x : (W₀.preimage g).toFunctor.obj A),
      g'.app A (φtrue.app A x) = g.app A x.val := fun A x =>
    ConcreteCategory.congr_hom (NatTrans.congr_app htrue_w A) x
  have hfalse_app : ∀ (A : (BigFppfOver B S hS)ᵒᵖ) (x : (pullback g f.hom).obj A),
      g'.app A (φfalse.app A x) = g.app A ((pullback.fst g f.hom).app A x) := fun A x =>
    ConcreteCategory.congr_hom (NatTrans.congr_app hfalse_w A) x
  -- Separation on the second member, from invertibility over the open complement.
  have hsep_false : ∀ (A : (BigFppfOver B S hS)ᵒᵖ) (x y : (pullback g f.hom).obj A),
      (pullback.fst g f.hom).app A x = (pullback.fst g f.hom).app A y →
      g.app A ((pullback.fst g f.hom).app A x) ∈ W₀.obj A →
      φfalse.app A x = φfalse.app A y := by
    intro A x y hxy hmem
    refine eq_of_app_eq_of_mem B S hS g' W₀ hisoX' ?_ ?_
    · rw [hfalse_app, hfalse_app, hxy]
    · rw [hfalse_app]; exact hmem
  -- The two fibre squares, evaluated at an object.
  have hVsq : ∀ A : (BigFppfOver B S hS)ᵒᵖ,
      IsPullback ((pullback.fst f.hom f.hom).app A) ((pullback.snd f.hom f.hom).app A)
        (f.hom.app A) (f.hom.app A) := fun A =>
    (IsPullback.of_hasPullback f.hom f.hom).map ((evaluation _ (Type u)).obj A)
  have hXsq : ∀ A : (BigFppfOver B S hS)ᵒᵖ,
      IsPullback ((pullback.fst g f.hom).app A) ((pullback.snd g f.hom).app A)
        (g.app A) (f.hom.app A) := fun A =>
    (IsPullback.of_hasPullback g f.hom).map ((evaluation _ (Type u)).obj A)
  have hXw : ∀ (A : (BigFppfOver B S hS)ᵒᵖ) (x : (pullback g f.hom).obj A),
      g.app A ((pullback.fst g f.hom).app A x)
        = f.hom.app A ((pullback.snd g f.hom).app A x) := by
    intro A x
    have h := ConcreteCategory.congr_hom (hXsq A).w x
    simpa only [ConcreteCategory.comp_apply, types_comp_apply] using h
  -- The hard case: one section of `X` with two lifts of its base point to `V`.
  have hhard : ∀ (Z : BigFppfOver B S hS) (x y : (pullback g f.hom).obj (op Z)),
      (pullback.fst g f.hom).app (op Z) x = (pullback.fst g f.hom).app (op Z) y →
      φfalse.app (op Z) x = φfalse.app (op Z) y := by
    intro Z x y hxy
    have hbase : f.hom.app (op Z) ((pullback.snd g f.hom).app (op Z) x)
        = f.hom.app (op Z) ((pullback.snd g f.hom).app (op Z) y) := by
      rw [← hXw, ← hXw, hxy]
    obtain ⟨s, hs₁, hs₂⟩ := Types.exists_of_isPullback (hVsq (op Z))
      ((pullback.snd g f.hom).app (op Z) x) ((pullback.snd g f.hom).app (op Z) y) hbase
    have hmem : (C ⊔ Subfunctor.range (pullback.diagonal f.hom)).sieveOfSection s ∈ J Z := by
      have hs : s ∈ ((C ⊔ Subfunctor.range (pullback.diagonal f.hom)).sheafify J).obj (op Z) := by
        rw [hcov]; trivial
      exact hs
    refine eq_of_locally_eq B S hS X'.property.1.isSheaf
      ((C ⊔ Subfunctor.range (pullback.diagonal f.hom)).sieveOfSection s) hmem ?_
    intro Y k hk
    rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply]
    have hfst' : (pullback.fst g f.hom).app (op Y) ((pullback g f.hom).map k.op x)
        = (pullback.fst g f.hom).app (op Y) ((pullback g f.hom).map k.op y) := by
      rw [NatTrans.naturality_apply, NatTrans.naturality_apply, hxy]
    have hsnd' : ∀ z : (pullback g f.hom).obj (op Z),
        (pullback.snd g f.hom).app (op Y) ((pullback g f.hom).map k.op z)
          = V.obj.map k.op ((pullback.snd g f.hom).app (op Z) z) := fun z =>
      NatTrans.naturality_apply (pullback.snd g f.hom) k.op z
    have hsfst : (pullback.fst f.hom f.hom).app (op Y) ((pullback f.hom f.hom).map k.op s)
        = V.obj.map k.op ((pullback.snd g f.hom).app (op Z) x) := by
      rw [NatTrans.naturality_apply, hs₁]
    have hssnd : (pullback.snd f.hom f.hom).app (op Y) ((pullback f.hom f.hom).map k.op s)
        = V.obj.map k.op ((pullback.snd g f.hom).app (op Z) y) := by
      rw [NatTrans.naturality_apply, hs₂]
    rcases hk with hkC | hkD
    · -- In `C`: the base point of the pair lies in the open complement.
      have hmem₀ := hC _ hkC
      change (pullback.fst f.hom f.hom ≫ f.hom).app (op Y)
        ((pullback f.hom f.hom).map k.op s) ∈ W₀.obj (op Y) at hmem₀
      rw [NatTrans.comp_app, ConcreteCategory.comp_apply, hsfst] at hmem₀
      refine hsep_false (op Y) _ _ hfst' ?_
      rw [hXw, hsnd']
      exact hmem₀
    · -- In the range of the diagonal: the two lifts coincide, so the sections coincide.
      obtain ⟨t, ht⟩ := hkD
      have hd : ∀ m : pullback f.hom f.hom ⟶ V.obj, pullback.diagonal f.hom ≫ m = 𝟙 _ →
          m.app (op Y) ((pullback f.hom f.hom).map k.op s) = t := fun m hm => by
        rw [← ht]
        exact ConcreteCategory.congr_hom (NatTrans.congr_app hm (op Y)) t
      have hvv : (pullback.snd g f.hom).app (op Y) ((pullback g f.hom).map k.op x)
          = (pullback.snd g f.hom).app (op Y) ((pullback g f.hom).map k.op y) := by
        rw [hsnd', hsnd', ← hsfst, ← hssnd, hd _ (pullback.diagonal_fst f.hom),
          hd _ (pullback.diagonal_snd f.hom)]
      rw [Types.ext_of_isPullback (hXsq (op Y)) hfst' hvv]
  -- The two members agree where a section of `X ×_W V` and one over `W⁰` have the same image.
  have hcross : ∀ (A : (BigFppfOver B S hS)ᵒᵖ) (x : (pullback g f.hom).obj A)
      (y : (W₀.preimage g).toFunctor.obj A),
      (pullback.fst g f.hom).app A x = y.val → φfalse.app A x = φtrue.app A y :=
    fun A x y hxy =>
    eq_of_app_eq_of_mem B S hS g' W₀ hisoX'
      ((hfalse_app A x).trans ((congrArg (g.app A) hxy).trans (htrue_app A y).symm))
      (Set.mem_of_eq_of_mem ((hfalse_app A x).trans (congrArg (g.app A) hxy)) y.2)
  -- Glue the two members into a morphism.
  obtain ⟨αleft, hα, -⟩ := glueHom J (excisionBaseMap B S hS f T g)
    (familyImage_excisionBaseMap_sieveOfSection_mem B S hS f T hT hfT hf g)
    X'.property.1.isSheaf
    (fun b => match b with | true => φtrue | false => φfalse)
    (by
      rintro Z (_ | _) (_ | _) x y hxy
      · change φfalse.app Z x = φfalse.app Z y
        exact hhard Z.unop x y hxy
      · exact hcross Z x y hxy
      · exact (hcross Z y x hxy.symm).symm
      · change φtrue.app Z x = φtrue.app Z y
        have hxyv : x = y := Subtype.ext hxy
        rw [hxyv])
  -- The glued morphism lies over `W`.
  have hαw : αleft ≫ g' = g := by
    refine hom_ext_of_familyImage_cover J (excisionBaseMap B S hS f T g)
      (familyImage_excisionBaseMap_sieveOfSection_mem B S hS f T hT hfT hf g)
      W'.property.isSheaf _ _ ?_
    rintro (_ | _)
    · rw [← Category.assoc, hα false]
      exact hfalse_w
    · rw [← Category.assoc, hα true]
      exact htrue_w
  have hαfalse : pullback.fst g f.hom ≫ αleft = φfalse := hα false
  refine ⟨ObjectProperty.homMk (Over.homMk αleft hαw), ?_⟩
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  have hfst : ((baseChangeFunctor B S hS f W₀).1.map
        (ObjectProperty.homMk (Over.homMk αleft hαw) : X ⟶ X')).hom.left
        ≫ pullback.fst g' f.hom = pullback.fst g f.hom ≫ αleft :=
    pullback.lift_fst _ _ _
  have hsnd : ((baseChangeFunctor B S hS f W₀).1.map
        (ObjectProperty.homMk (Over.homMk αleft hαw) : X ⟶ X')).hom.left
        ≫ pullback.snd g' f.hom = pullback.snd g f.hom :=
    pullback.lift_snd _ _ _
  refine pullback.hom_ext ?_ ?_
  · exact hfst.trans (hαfalse.trans (hφfalse.trans
      (congrArg (fun m => m ≫ pullback.fst g' f.hom) hβleft)))
  · exact hsnd.trans
      (((congrArg (fun m => m ≫ pullback.snd g' f.hom) hβleft).symm.trans hβw).symm)

/-- **Stacks 0BGY, fullness of the base-change functor.** Let `f : V ⟶ W` be a separated étale
morphism of algebraic spaces over `S` and let `T` be a closed subspace of `W` whose preimage is
carried isomorphically onto `T`. Then the functor of Stacks 0BGY, base change along `f` from the
modifications of `W` outside the open complement `W⁰` of `T` to the modifications of `V` outside
`f⁻¹W⁰`, is full. -/
@[stacks 0BGY "the base-change functor is full"]
theorem full_baseChangeFunctor (f : V ⟶ W') (T : Subfunctor W'.obj)
    (hT : IsClosedSubspace B S hS T) (hfT : IsIso (T.fromPreimage f.hom))
    (hf : IsEtale B S hS f.hom) (hsep : IsSeparated B S hS f.hom) :
    (baseChangeFunctor B S hS f (openComplement B S hS T)).1.Full := by
  obtain ⟨C, hcov, hC, -⟩ := exists_subfunctor_sheafify_sup_range_diagonal_eq_top B S hS
    V.property W'.property f.hom hf hsep T hfT
  rw [sup_comm] at hcov
  exact full_baseChangeFunctor_of_diagonalComplement B S hS f T hT hfT hf C hC hcov

/-- **Stacks 0BGY, full faithfulness of the base-change functor.** -/
@[stacks 0BGY "the base-change functor is fully faithful"]
noncomputable def fullyFaithful_baseChangeFunctor (f : V ⟶ W') (T : Subfunctor W'.obj)
    (hT : IsClosedSubspace B S hS T) (hfT : IsIso (T.fromPreimage f.hom))
    (hf : IsEtale B S hS f.hom) (hsep : IsSeparated B S hS f.hom) :
    (baseChangeFunctor B S hS f (openComplement B S hS T)).1.FullyFaithful :=
  have := faithful_baseChangeFunctor B S hS f T hT hfT hf
  have := full_baseChangeFunctor B S hS f T hT hfT hf hsep
  Functor.FullyFaithful.ofFullyFaithful _

end AlgebraicGeometry.Space

end
