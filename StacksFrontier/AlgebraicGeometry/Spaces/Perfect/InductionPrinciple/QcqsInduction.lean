module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.InductionPrinciple.SchemeCase
import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.Dimension

/-!
# Induction on quasi-compact quasi-separated algebraic spaces

The property is inherited across an elementary distinguished square whose étale member is a
scheme; the steps of a finite filtration by open subspaces are elementary distinguished
squares; and the induction principle itself.

## Main results

* `AlgebraicGeometry.Space.qcqs_induction_on` is **Stacks 08GP**.
* `AlgebraicGeometry.Space.qcqs_induction_on_self` is the case of the base space.
* `AlgebraicGeometry.Space.qcqs_induction_on_collection` is **Stacks 08GQ**.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-- If affine opens in `s` cover a site object `T`, every point of `T` lies in the image of one
of the open subobjects of `T` they define. -/
private theorem exists_mem_range_pointsMap_representableOpenSubobject_of_iSup_eq_top
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (T : BigFppfOver B S hS)
    (s : Set ((BigFppfOver.toScheme B S hS).obj T).affineOpens)
    (hcover : ⊤ = ⨆ A ∈ s, (A : ((BigFppfOver.toScheme B S hS).obj T).Opens))
    (y : points B S hS (yoneda.obj T)) :
    ∃ A ∈ s, y ∈ Set.range (pointsMap B S hS
      (representableOpenSubobject B S hS T A).toFunctor
      (representableOpenSubobject B S hS T A).ι) := by
  induction y using Quot.inductionOn with | h p =>
    have hx : (BigFppfOver.toScheme B S hS).map p.value (IsLocalRing.closedPoint p.carrier) ∈
        (⨆ A ∈ s, (A : ((BigFppfOver.toScheme B S hS).obj T).Opens)) := by
      rw [← hcover]
      trivial
    simp only [TopologicalSpace.Opens.mem_iSup] at hx
    obtain ⟨A, hAs, hA⟩ := hx
    have hmem : p.value ∈ (representableOpenSubobject B S hS T A).obj
        (Opposite.op p.siteObject) := by
      rw [mem_representableOpenSubobject_iff]
      rintro z ⟨a, rfl⟩
      have ha : a = IsLocalRing.closedPoint p.carrier :=
        (inferInstance : Subsingleton (PrimeSpectrum p.carrier)).elim _ _
      rwa [ha]
    let p' : FieldValuedPoint B S hS
        (representableOpenSubobject B S hS T A).toFunctor :=
      { carrier := p.carrier, contained := p.contained, toBase := p.toBase,
        value := ⟨p.value, hmem⟩ }
    exact ⟨A, hAs, p'.class, rfl⟩

/-- The isomorphism-invariant form of `P` transfers along an isomorphism compatible with the
structure morphisms. -/
private theorem propertyUpToIso_of_iso
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)
    (P : (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) → (Y ⟶ X.1) → Prop)
    {F F' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {g : F ⟶ X.1} {g' : F' ⟶ X.1} (e : F ≅ F')
    (h : propertyUpToIso B S hS X P F' g') (hg : e.hom ≫ g' = g) :
    propertyUpToIso B S hS X P F g := by
  intro Z eZ
  simpa [hg] using h Z (eZ ≪≫ e)

/-- The isomorphism-invariant form of `P` passes across an elementary distinguished square
whose étale member is a quasi-compact quasi-separated scheme surjective on points. -/
private theorem propertyUpToIso_of_elementarySquare_scheme
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS)
    (P : (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) →
      (Y ⟶ X.1) → Prop)
    (haff : ∀ V : SpacesEtale B S hS X,
      IsAffineSpace B S hS V.1.left.1 → P V.1.left.1 V.1.hom.hom)
    (hstep : ∀ (W V : SpacesEtale B S hS X)
      (U : Subfunctor W.1.left.1)
      (f : V.1.left.1 ⟶ W.1.left.1),
      f ≫ W.1.hom.hom = V.1.hom.hom →
      IsElementaryDistinguishedSquare B S hS W.1.left.property U f →
      IsQuasiCompactSpace B S hS W.1.left.1 →
      IsAbsolutelyQuasiSeparated B S hS hZ W.1.left.1 →
      IsQuasiCompactSpace B S hS U.toFunctor →
      IsAffineSpace B S hS V.1.left.1 →
      P U.toFunctor (U.ι ≫ W.1.hom.hom) →
      P V.1.left.1 V.1.hom.hom →
      P (pullback U.ι f)
        (pullback.fst U.ι f ≫ U.ι ≫ W.1.hom.hom) →
      P W.1.left.1 W.1.hom.hom)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F)
    (hFqs : IsAbsolutelyQuasiSeparated B S hS hZ F)
    (g : F ⟶ X.1) (hg : IsEtale B S hS g)
    (T : BigFppfOver B S hS)
    (hTqc : CompactSpace ((BigFppfOver.toScheme B S hS).obj T))
    (hTqs : IsAbsolutelyQuasiSeparated B S hS hZ (yoneda.obj T))
    (U : Subfunctor F) (f : yoneda.obj T ⟶ F)
    (hsq : IsElementaryDistinguishedSquare B S hS hF U f)
    (hsurj : Function.Surjective (pointsMap B S hS (yoneda.obj T) f))
    (hUqc : IsQuasiCompactSpace B S hS U.toFunctor)
    (hQU : propertyUpToIso B S hS X P U.toFunctor (U.ι ≫ g)) :
    propertyUpToIso B S hS X P F g := by
  classical
  let q := BigFppfOver.toScheme B S hS
  let := hTqc
  obtain ⟨s, hs, hcover⟩ :=
    (isCompact_iff_finite_and_eq_biUnion_affineOpens (X := q.obj T)
      (U := ⊤)).mp isCompact_univ
  have hfinite (t : Finset (q.obj T).affineOpens) :
      ∃ (D : Subfunctor F) (hD : IsOpenSubspace B S hS D),
        U ≤ D ∧ IsQuasiCompactSpace B S hS D.toFunctor ∧
        propertyUpToIso B S hS X P D.toFunctor (D.ι ≫ g) ∧
        ∀ A ∈ t, Set.range (pointsMap B S hS
          (representableOpenSubobject B S hS T A).toFunctor
          ((representableOpenSubobject B S hS T A).ι ≫ f)) ⊆
          Set.range (pointsMap B S hS D.toFunctor D.ι) := by
    induction t using Finset.induction_on with
    | empty => exact ⟨U, hsq.isOpenSubspace, le_rfl, hUqc, hQU, by simp⟩
    | @insert A t hAt ih =>
      obtain ⟨C, hC, hUC, hCqc, hQC, hCt⟩ := ih
      obtain ⟨D, hD, hCD, hDqc, hQD, hrange⟩ :=
        propertyUpToIso_extend_affine B S hS hZ X P haff hstep hF hFqs g hg T hTqs
          U f hsq C hC hUC hCqc hQC A
      refine ⟨D, hD, hUC.trans hCD, hDqc, hQD, ?_⟩
      intro A' hA'
      rcases Finset.mem_insert.mp hA' with rfl | hA'
      · rw [hrange]
        exact Set.subset_union_right
      · exact (hCt A' hA').trans (pointsRange_mono B S hS hCD)
  obtain ⟨D, hD, hUD, hDqc, hQD, hDs⟩ := hfinite hs.toFinset
  have hrange : Set.range (pointsMap B S hS D.toFunctor D.ι) = Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨y, rfl⟩ := hsurj x
    obtain ⟨A, hAs, z, rfl⟩ :=
      exists_mem_range_pointsMap_representableOpenSubobject_of_iSup_eq_top B S hS T s hcover y
    apply hDs A (hs.mem_toFinset.mpr hAs)
    exact ⟨z, congrFun (pointsMap_comp B S hS _ _ f) z⟩
  have hDtop : D = ⊤ := openSubspace_eq_of_pointsMap_range_eq B S hS hF D ⊤ hD
    (isOpenSubspace_top hF)
    (hrange.trans (Set.range_eq_univ.mpr
      (pointsMap_surjective_of_iso B S hS (asIso (⊤ : Subfunctor F).ι))).symm)
  rw [hDtop] at hQD
  exact propertyUpToIso_of_iso B S hS X P (asIso (⊤ : Subfunctor F).ι).symm hQD
    (by simp)

/-- The presheaf represented by an object of the site with quasi-separated underlying scheme is
absolutely quasi-separated. -/
private theorem isQuasiSeparated_yoneda
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u})) (T : BigFppfOver B S hS)
    (hT : QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj T)) :
    IsAbsolutelyQuasiSeparated B S hS hZ (yoneda.obj T) := by
  let b : B.obj hS ⟶ B.obj hZ := ⟨terminal.from S⟩
  let T' : BigFppfOver B (⊤_ Scheme.{u}) hZ := Over.mk (T.hom ≫ b)
  let e : (OverShriek.relocalizePresheafFunctor b).obj (yoneda.obj T) ≅ yoneda.obj T' :=
    (Functor.representableByEquiv
      (yonedaRelocalizedRepresentableBy B S (⊤_ Scheme.{u}) hS hZ b T)).symm
  exact qs_preserved_by_iso B (⊤_ Scheme.{u}) hZ e.symm
    (isQuasiSeparated_yoneda_of_quasiSeparatedSpace B hZ T' hT)

/-- If the image under an injection of the range of `b` is the range of that injection minus
the image of the range of `c`, then the range of `b` is the complement of the range of `c`. -/
private theorem range_eq_compl_of_range_comp_eq_diff
    {A B C D : Type*} (a : A → B) (b : C → A) (c : D → A)
    (ha : Function.Injective a)
    (h : Set.range (a ∘ b) = Set.range a \ Set.range (a ∘ c)) :
    Set.range b = (Set.range c)ᶜ := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩ ⟨z, hz⟩
    have hy : a (b y) ∈ Set.range a \ Set.range (a ∘ c) := h ▸ ⟨y, rfl⟩
    exact hy.2 ⟨z, congrArg a hz⟩
  · intro hx
    have hx' : a x ∈ Set.range a \ Set.range (a ∘ c) := by
      refine ⟨⟨x, rfl⟩, ?_⟩
      rintro ⟨z, hz⟩
      exact hx ⟨z, ha hz⟩
    obtain ⟨y, hy⟩ := h.symm ▸ hx'
    exact ⟨y, ha hy⟩

/-- A closed subspace of an open subspace whose points are those of the larger open subspace
not in the smaller one is supported on the complement of the smaller one inside the larger. -/
private theorem nested_closed_support
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F)
    (I J : Subfunctor F) (hJ : IsOpenSubspace B S hS J)
    (hIJ : I ≤ J) (T : Subfunctor J.toFunctor)
    (hsupport : Set.range (pointsMap B S hS T.toFunctor (T.ι ≫ J.ι)) =
      Set.range (pointsMap B S hS J.toFunctor J.ι) \
      Set.range (pointsMap B S hS I.toFunctor I.ι)) :
    Set.range (pointsMap B S hS T.toFunctor T.ι) =
      (Set.range (pointsMap B S hS
        (Subfunctor.range (Subfunctor.homOfLe hIJ)).toFunctor
        (Subfunctor.range (Subfunctor.homOfLe hIJ)).ι))ᶜ := by
  let C := Subfunctor.range (Subfunctor.homOfLe hIJ)
  let e : I.toFunctor ≅ C.toFunctor := asIso (Subfunctor.toRange (Subfunctor.homOfLe hIJ))
  have hcomp : e.hom ≫ C.ι ≫ J.ι = I.ι := by
    simp only [e, C, asIso_hom, ← Category.assoc, Subfunctor.toRange_ι,
      Subfunctor.homOfLe_ι]
  have hrange : Set.range (pointsMap B S hS C.toFunctor (C.ι ≫ J.ι)) =
      Set.range (pointsMap B S hS I.toFunctor I.ι) := by
    rw [← hcomp, pointsMap_comp B S hS _ e.hom (C.ι ≫ J.ι), Set.range_comp,
      Set.range_eq_univ.mpr (pointsMap_surjective_of_iso B S hS e), Set.image_univ]
  let := pointTopology B S hS F
  let := pointTopology B S hS J.toFunctor
  have hinj := (isEmbedding_pointsMap_of_isImmersion B S hS hF J.ι
    (immersion_of_openImmersion B S hS hJ.2)).injective
  refine range_eq_compl_of_range_comp_eq_diff _ _ _ hinj ?_
  rwa [← pointsMap_comp, ← pointsMap_comp, hrange]

/-- The empty sieve covers an object of the big fppf category over `S` whose underlying scheme
is empty. -/
private theorem bot_mem_bigFppfOverTopology_of_isEmpty
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hE : B.Contains (∅ : Scheme.{u}))
    (T : BigFppfOver B S hS)
    (hT : T.left = B.obj hE) :
    (⊥ : Sieve T) ∈ BigFppfOver.topology B S hS T := by
  have hb : (⊥ : Sieve T.left) ∈ B.topology T.left :=
    hT.symm ▸ AlgebraicGeometry.BigFppfSite.bot_mem_topology_obj_contains_empty B hE
  rw [BigFppfOver.topology, GrothendieckTopology.mem_over_iff]
  simpa using hb

/-- The empty sieve covers the empty object of the big fppf category over `S`. -/
private theorem initialObj_bot_mem
    (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    (⊥ : Sieve (BigFppfOver.initialObj B S hS)) ∈
      BigFppfOver.topology B S hS (BigFppfOver.initialObj B S hS) := by
  have hE : B.Contains (∅ : Scheme.{u}) :=
    lt_of_le_of_lt AlgebraicGeometry.Scheme.size_empty_le_aleph0 B.aleph0_lt_cutoff
  apply bot_mem_bigFppfOverTopology_of_isEmpty B S hS hE
    (BigFppfOver.initialObj B S hS)
  dsimp [BigFppfOver.initialObj]

/-- The sheafification of the bottom subfunctor of an algebraic space is the presheaf
represented by the empty object of the site. -/
private noncomputable def emptySubspaceIso
    (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X) :
    ((⊥ : Subfunctor X).sheafify
      (BigFppfOver.topology B S hS)).toFunctor ≅
        yoneda.obj (BigFppfOver.initialObj B S hS) := by
  let J := BigFppfOver.topology B S hS
  let bot : Subfunctor X := ⊥
  let I := bot.sheafify J
  have hX' : Presieve.IsSheaf J X := (isSheaf_iff_isSheaf_of_type J X).mp hX.isSheaf
  have hI : Presieve.IsSheaf J I.toFunctor := bot.sheafify_isSheaf hX'
  have hEY : Presheaf.IsSheaf J (yoneda.obj (BigFppfOver.initialObj B S hS)) :=
    (isAlgebraicSpace_yoneda B S hS (BigFppfOver.initialObj B S hS)).isSheaf
  let eI : Sheaf J (Type u) := ⟨I.toFunctor,
    (isSheaf_iff_isSheaf_of_type J _).mpr hI⟩
  let eE : Sheaf J (Type u) := ⟨yoneda.obj (BigFppfOver.initialObj B S hS), hEY⟩
  have hIunique (a b : I.toFunctor ⟶ I.toFunctor) : a = b := by
    apply bot.to_sheafify_lift_unique hI
    ext T x
    exact (Set.notMem_empty _ x.property).elim
  have hEterm : IsTerminal (eE.1.obj (Opposite.op (BigFppfOver.initialObj B S hS))) :=
    Sheaf.isTerminalOfBotCover eE _ (initialObj_bot_mem B S hS)
  have hEunique (a b : eE.1 ⟶ eE.1) : a = b := by
    apply yonedaEquiv.injective
    let : Unique (eE.1.obj (Opposite.op (BigFppfOver.initialObj B S hS))) :=
      Types.isTerminalEquivUnique _ hEterm
    exact Subsingleton.elim _ _
  let f0 : bot.toFunctor ⟶ eE.1 := {
    app T := ↾fun x => (Set.notMem_empty _ x.property).elim
    naturality := by
      intro T T' f
      ext x
      exact (Set.notMem_empty _ x.property).elim
  }
  let f : eI.1 ⟶ eE.1 := bot.sheafifyLift f0 ((isSheaf_iff_isSheaf_of_type J _).mp hEY)
  let x : eI.1.obj (Opposite.op (BigFppfOver.initialObj B S hS)) := by
    letI : Unique (eI.1.obj (Opposite.op (BigFppfOver.initialObj B S hS))) :=
      Types.isTerminalEquivUnique _
        (Sheaf.isTerminalOfBotCover eI _ (initialObj_bot_mem B S hS))
    exact default
  let g : eE.1 ⟶ eI.1 := yonedaEquiv.symm x
  exact ⟨f, g, hIunique _ _, hEunique _ _⟩

/-- The sheafification of the bottom subfunctor of an algebraic space is isomorphic to the
presheaf represented by the empty object of the site: the last term of a finite filtration
supplied by `AlgebraicGeometry.Space.exists_finiteFiltration_of_isQuasiCompactSpace` is the
empty algebraic space. -/
theorem nonempty_sheafify_bot_iso_initialObj
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X) :
    Nonempty (((⊥ : Subfunctor X).sheafify (BigFppfOver.topology B S hS)).toFunctor ≅
      yoneda.obj (BigFppfOver.initialObj B S hS)) :=
  ⟨emptySubspaceIso B S hS X hX⟩

attribute [-instance] CategoryTheory.Limits.Types.instHasPushoutsType in
/-- One step of a finite filtration by open subspaces is an elementary distinguished square.
Let `I ≤ J` be open subspaces of an algebraic space `F`, let `T` be a reduced closed subspace
of `J` whose points are those of `J` not in `I`, and let `f : V ⟶ J` be étale and an
isomorphism above `T`. Then `I`, read as an open subspace of `J`, and `f` form an elementary
distinguished square on `J`. This is how the steps of the filtration of Stacks 07ST feed the
induction of Stacks 08GP. -/
theorem isElementaryDistinguishedSquare_of_reducedStratum
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hV : IsAlgebraicSpace B S hS V)
    (I J : Subfunctor F) (hI : IsOpenSubspace B S hS I) (hJ : IsOpenSubspace B S hS J)
    (hIJ : I ≤ J) (T : Subfunctor J.toFunctor) (hT : IsClosedSubspace B S hS T)
    (hTsupport : Set.range (pointsMap B S hS T.toFunctor (T.ι ≫ J.ι)) =
      Set.range (pointsMap B S hS J.toFunctor J.ι) \
      Set.range (pointsMap B S hS I.toFunctor I.ι))
    (hTred : HasEtaleLocalProperty B S hS T.toFunctor
      (fun Y : Scheme.{u} => IsReduced Y))
    (f : V ⟶ J.toFunctor) (hf : IsEtale B S hS f)
    (hpb : IsIso (pullback.fst T.ι f)) :
    IsElementaryDistinguishedSquare B S hS hJ.1
      (Subfunctor.range (Subfunctor.homOfLe hIJ)) f :=
  elementarySquare_of_reduced_closed_complement B S hS hJ.1 hV _
    (isOpenSubspace_of_le B S hS I J hI hIJ) T hT hTred
    (nested_closed_support B S hS hF I J hJ hIJ T hTsupport) f hf hpb

attribute [-instance] CategoryTheory.Limits.Types.instHasPushoutsType in

/-- **Stacks 08GP.** Induction on the quasi-compact quasi-separated objects of the
spaces-étale site of a quasi-compact quasi-separated algebraic space `X`: a property of
algebraic spaces étale over `X` which holds on the affine ones and is inherited across an
elementary distinguished square with affine étale member holds on all of them. -/
@[stacks 08GP "every quasi-compact quasi-separated étale object"]
public theorem qcqs_induction_on
    (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS)
    (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (P : (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) →
      (Y ⟶ X.1) → Prop)
    (haff : ∀ V : SpacesEtale B S hS X,
      IsAffineSpace B S hS V.1.left.1 →
        P V.1.left.1 V.1.hom.hom)
    (hstep : ∀ (W V : SpacesEtale B S hS X)
      (U : Subfunctor W.1.left.1)
      (f : V.1.left.1 ⟶ W.1.left.1),
      (f ≫ W.1.hom.hom = V.1.hom.hom) →
      IsElementaryDistinguishedSquare B S hS W.1.left.property U f →
      IsQuasiCompactSpace B S hS W.1.left.1 →
      IsAbsolutelyQuasiSeparated B S hS hZ W.1.left.1 →
      IsQuasiCompactSpace B S hS U.toFunctor →
      IsAffineSpace B S hS V.1.left.1 →
      P U.toFunctor (U.ι ≫ W.1.hom.hom) →
      P V.1.left.1 V.1.hom.hom →
      P (pullback U.ι f)
        (pullback.fst U.ι f ≫ U.ι ≫ W.1.hom.hom) →
      P W.1.left.1 W.1.hom.hom) :
    ∀ Y : SpacesEtale B S hS X,
      IsQuasiCompactSpace B S hS Y.1.left.1 →
      IsAbsolutelyQuasiSeparated B S hS hZ Y.1.left.1 →
      P Y.1.left.1 Y.1.hom.hom := by
  classical
  intro Y hYqc hYqs
  obtain ⟨n, U, hn, hUzero, hUn, hUopen, hUnested, hfiltration⟩ :=
    exists_finiteFiltration_of_isQuasiCompactSpace
      B S hS hZ Y.1.left.1 Y.1.left.property hYqc hYqs
  let E := BigFppfOver.initialObj B S hS
  let e0 := emptySubspaceIso B S hS Y.1.left.1 Y.1.left.property
  let e : (U n).toFunctor ≅ yoneda.obj E :=
    eqToIso (congrArg Subfunctor.toFunctor hUn) ≪≫ e0
  let g : yoneda.obj E ⟶ Y.1.left.1 := e.inv ≫ (U n).ι
  have hmap : e.hom ≫ g = (U n).ι := by
    simp [g]
  have hgfac : e.inv ≫ (U n).ι = g := by
    rfl
  have hgopen : IsOpenImmersion B S hS g := by
    let Q := MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)
    let : Q.presheaf.RespectsIso := MorphismProperty.relative_respectsIso Q
    rw [← hgfac]
    exact MorphismProperty.RespectsIso.precomp Q.presheaf e.inv (U n).ι
      (hUopen n (Nat.le_refl n)).2
  let Vempty : SpacesEtale B S hS X :=
    siteObjectOfEtaleMap B S hS X (yoneda.obj E)
      (isAlgebraicSpace_yoneda B S hS E)
      (g ≫ Y.1.hom.hom)
      (isEtale_comp B S hS
        (etale_of_openImmersion B S hS g hgopen) Y.2)
  have hVemptyAff : IsAffineSpace B S hS Vempty.1.left.1 := by
    refine ⟨E, ?_, ⟨Iso.refl _⟩⟩
    show IsAffine (∅ : Scheme.{u})
    infer_instance
  have hQVempty := propertyUpToIso_of_affine B S hS X P haff Vempty hVemptyAff
  have hQn : propertyUpToIso B S hS X P (U n).toFunctor
      ((U n).ι ≫ Y.1.hom.hom) := by
    exact propertyUpToIso_of_iso B S hS X P (g' := g ≫ Y.1.hom.hom) e hQVempty
      (by simp [g])
  obtain ⟨T, V, f, hdata⟩ := hfiltration
  have hUqc (p : ℕ) (hp : p ≤ n) :
      IsQuasiCompactSpace B S hS (U p).toFunctor := by
    rcases lt_or_eq_of_le hp with hp | rfl
    · exact ⟨V ⟨p, hp⟩, f ⟨p, hp⟩, (hdata ⟨p, hp⟩).2.2.2.1,
        (hdata ⟨p, hp⟩).2.2.2.2.2.1, (hdata ⟨p, hp⟩).2.2.2.2.2.2.1⟩
    · exact IsQuasiCompactSpace.of_iso B S hS
        (isQuasiCompactSpace_yonedaObj_of_compactSpace B S hS E
          (show CompactSpace (∅ : Scheme.{u}) from inferInstance)) e.symm
  have hdesc (p : ℕ) (hp : p ≤ n) :
      propertyUpToIso B S hS X P (U p).toFunctor ((U p).ι ≫ Y.1.hom.hom) := by
    induction hp using Nat.decreasingInduction with
    | self => exact hQn
    | of_succ p hp ih =>
      let i : Fin n := ⟨p, hp⟩
      obtain ⟨hTclosed, hTsupport, hTred, hVcompact, hVsep, hsurj, hf, hpb⟩ := hdata i
      have hUp := hUopen p (Nat.le_of_lt hp)
      have hUqs := openSubspace_isQuasiSeparated B S hS hZ
        Y.1.left.property hYqs (U p) hUp
      let C := Subfunctor.range (Subfunctor.homOfLe (hUnested p hp))
      have hsq := isElementaryDistinguishedSquare_of_reducedStratum B S hS
        Y.1.left.property (isAlgebraicSpace_yoneda B S hS (V i)) (U (p + 1)) (U p)
        (hUopen (p + 1) hp) hUp (hUnested p hp) (T i) hTclosed hTsupport hTred (f i) hf hpb
      let eC : (U (p + 1)).toFunctor ≅ C.toFunctor :=
        asIso (Subfunctor.toRange (Subfunctor.homOfLe (hUnested p hp)))
      have hQC : propertyUpToIso B S hS X P C.toFunctor
          (C.ι ≫ (U p).ι ≫ Y.1.hom.hom) := by
        have hinc : eC.inv ≫ (U (p + 1)).ι = C.ι ≫ (U p).ι := by
          rw [← Subfunctor.homOfLe_ι (hUnested p hp),
            ← Subfunctor.toRange_ι (Subfunctor.homOfLe (hUnested p hp))]
          show ((eC.inv ≫ eC.hom) ≫ C.ι) ≫ (U p).ι = C.ι ≫ (U p).ι
          rw [eC.inv_hom_id, Category.id_comp]
        refine propertyUpToIso_of_iso B S hS X P eC.symm ih ?_
        simpa only [Iso.symm_hom, Category.assoc] using
          congrArg (fun k => k ≫ Y.1.hom.hom) hinc
      have hVqs : IsAbsolutelyQuasiSeparated B S hS hZ (yoneda.obj (V i)) := by
        let := hVsep
        exact isQuasiSeparated_yoneda B S hS hZ (V i) inferInstance
      exact propertyUpToIso_of_elementarySquare_scheme B S hS hZ X P haff hstep
        hUp.1 hUqs ((U p).ι ≫ Y.1.hom.hom)
        (isEtale_comp B S hS (etale_of_openImmersion B S hS (U p).ι hUp.2) Y.2)
        (V i) hVcompact hVqs C (f i) hsq
        ((presheafSurjective_iff_isSurjective_yoneda B S hS (U p).toFunctor hUp.1
          (V i) (f i)).mp hsurj)
        (IsQuasiCompactSpace.of_iso B S hS (hUqc (p + 1) hp) eC) hQC
  have hQzero := hdesc 0 (Nat.zero_le n)
  rw [hUzero] at hQzero
  simpa using hQzero Y.1.left.1 (asIso (⊤ : Subfunctor Y.1.left.1).ι).symm

attribute [-instance] CategoryTheory.Limits.Types.instHasPushoutsType in
/-- **Stacks 08GP** for the base space: a property of algebraic spaces étale over a
quasi-compact quasi-separated algebraic space `X` which holds on the affine ones and is
inherited across an elementary distinguished square with affine étale member holds for `X`
itself, taken with its identity morphism. -/
@[stacks 08GP "the base space"]
public theorem qcqs_induction_on_self
    (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS)
    (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (P : (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) →
      (Y ⟶ X.1) → Prop)
    (haff : ∀ V : SpacesEtale B S hS X,
      IsAffineSpace B S hS V.1.left.1 →
        P V.1.left.1 V.1.hom.hom)
    (hstep : ∀ (W V : SpacesEtale B S hS X)
      (U : Subfunctor W.1.left.1)
      (f : V.1.left.1 ⟶ W.1.left.1),
      (f ≫ W.1.hom.hom = V.1.hom.hom) →
      IsElementaryDistinguishedSquare B S hS W.1.left.property U f →
      IsQuasiCompactSpace B S hS W.1.left.1 →
      IsAbsolutelyQuasiSeparated B S hS hZ W.1.left.1 →
      IsQuasiCompactSpace B S hS U.toFunctor →
      IsAffineSpace B S hS V.1.left.1 →
      P U.toFunctor (U.ι ≫ W.1.hom.hom) →
      P V.1.left.1 V.1.hom.hom →
      P (pullback U.ι f)
        (pullback.fst U.ι f ≫ U.ι ≫ W.1.hom.hom) →
      P W.1.left.1 W.1.hom.hom) :
    P X.1 (𝟙 X.1) := by
  let Y : SpacesEtale B S hS X :=
    ⟨Over.mk (𝟙 X), by intro T φ hφ; simpa using hφ⟩
  simpa [Y] using qcqs_induction_on B S hS hZ X hXqc hXqs P haff hstep Y hXqc hXqs

/-- **Stacks 08GQ.** Induction inside a collection `𝓑` of objects of the spaces-étale site of
a quasi-compact quasi-separated algebraic space `X`: a property of the members of `𝓑` holds
throughout `𝓑` as soon as `𝓑` consists of quasi-compact quasi-separated objects, is closed
under quasi-compact open subspaces and contains every affine object, the property holds on
the affine objects, and it is inherited across an elementary distinguished square whose
ambient object lies in `𝓑` and whose étale member is affine. -/
@[stacks 08GQ]
public theorem qcqs_induction_on_collection
    (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS)
    (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (𝓑 P : (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) →
      (Y ⟶ X.1) → Prop)
    (hBqcqs : ∀ W : SpacesEtale B S hS X,
      𝓑 W.1.left.1 W.1.hom.hom →
      IsQuasiCompactSpace B S hS W.1.left.1 ∧
        IsAbsolutelyQuasiSeparated B S hS hZ W.1.left.1)
    (hBopen : ∀ (W : SpacesEtale B S hS X)
      (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (i : U ⟶ W.1.left.1),
      𝓑 W.1.left.1 W.1.hom.hom →
      IsAlgebraicSpace B S hS U →
      IsOpenImmersion B S hS i →
      IsQuasiCompactSpace B S hS U →
      𝓑 U (i ≫ W.1.hom.hom))
    (hBaff : ∀ V : SpacesEtale B S hS X,
      IsAffineSpace B S hS V.1.left.1 →
        𝓑 V.1.left.1 V.1.hom.hom)
    (hPaff : ∀ V : SpacesEtale B S hS X,
      IsAffineSpace B S hS V.1.left.1 →
        P V.1.left.1 V.1.hom.hom)
    (hstep : ∀ (W V : SpacesEtale B S hS X)
      (U : Subfunctor W.1.left.1)
      (f : V.1.left.1 ⟶ W.1.left.1),
      (f ≫ W.1.hom.hom = V.1.hom.hom) →
      IsElementaryDistinguishedSquare B S hS W.1.left.property U f →
      𝓑 W.1.left.1 W.1.hom.hom →
      IsQuasiCompactSpace B S hS U.toFunctor →
      IsAffineSpace B S hS V.1.left.1 →
      P U.toFunctor (U.ι ≫ W.1.hom.hom) →
      P V.1.left.1 V.1.hom.hom →
      P (pullback U.ι f)
        (pullback.fst U.ι f ≫ U.ι ≫ W.1.hom.hom) →
      P W.1.left.1 W.1.hom.hom) :
    ∀ W : SpacesEtale B S hS X,
      𝓑 W.1.left.1 W.1.hom.hom →
      P W.1.left.1 W.1.hom.hom := by
  intro W hBW
  refine qcqs_induction_on B S hS hZ X hXqc hXqs (fun Y g => 𝓑 Y g → P Y g)
    (fun V hVaff _ => hPaff V hVaff) ?_ W (hBqcqs W hBW).1 (hBqcqs W hBW).2 hBW
  intro W' V U f hcomp hsq _hW'qc hW'qs hUqc hVaff hQU hQV hQpb hBW'
  have hVqc : IsQuasiCompactSpace B S hS V.1.left.1 :=
    IsAffineSpace.isQuasiCompactSpace hVaff
  have hpbqc : IsQuasiCompactSpace B S hS (pullback U.ι f) :=
    isQuasiCompactSpace_pullback B S hS hZ U.ι f hsq.isOpenSubspace.1
      W'.1.left.property hUqc hVqc hW'qs
  have hpbalg : IsAlgebraicSpace B S hS (pullback U.ι f) :=
    isAlgebraicSpace_pullback B S hS U.ι f hsq.isOpenSubspace.1
      V.1.left.property W'.1.left.property
  have hpbopen : IsOpenImmersion B S hS (pullback.snd U.ι f) := by
    let Q : MorphismProperty (BigFppfOver B S hS) :=
      MorphismProperty.inverseImage
        (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)
    let _ : Q.presheaf.IsStableUnderBaseChange :=
      MorphismProperty.relative_isStableUnderBaseChange Q
    show Q.presheaf (pullback.snd U.ι f)
    exact MorphismProperty.pullback_snd (P := Q.presheaf) U.ι f hsq.isOpenSubspace.2
  have hpbmap : pullback.fst U.ι f ≫ U.ι ≫ W'.1.hom.hom =
      pullback.snd U.ι f ≫ V.1.hom.hom := by
    calc pullback.fst U.ι f ≫ U.ι ≫ W'.1.hom.hom
        = (pullback.snd U.ι f ≫ f) ≫ W'.1.hom.hom := by
          rw [← Category.assoc, pullback.condition]
      _ = pullback.snd U.ι f ≫ V.1.hom.hom := by rw [Category.assoc, hcomp]
  have hBpb : 𝓑 (pullback U.ι f)
      (pullback.fst U.ι f ≫ U.ι ≫ W'.1.hom.hom) := by
    rw [hpbmap]
    exact hBopen V (pullback U.ι f) (pullback.snd U.ι f) (hBaff V hVaff)
      hpbalg hpbopen hpbqc
  exact hstep W' V U f hcomp hsq hBW' hUqc hVaff
    (hQU (hBopen W' U.toFunctor U.ι hBW' hsq.isOpenSubspace.1
      hsq.isOpenSubspace.2 hUqc))
    (hQV (hBaff V hVaff)) (hQpb hBpb)

end AlgebraicGeometry.Space

end
