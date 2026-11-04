module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Restriction
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceComparison
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.SquareFlatPullback
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.SquarePushforward
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.GeneralRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceAssembly.BaseChangePieces

/-!
# The zero scheme of a pulled-back section along the pieces of a base change

The second of the four parts of
`StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceAssembly`; the overview, the
implementation notes and the references for Stacks 0FDZ are at the top of its first part,
`StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceAssembly.BaseChangePieces`.

Given a test scheme `g : T ⟶ Y`, an invertible module `L` on `T` and a section `s`, this part
decomposes the zero scheme of the section pulled back to `X ×_Y T` along the pieces
`X_i ×_{Y_{a(i)}} T_{a(i)}` (`Stacks.Chow.zeroSchemePiece`,
`Stacks.Chow.zeroSchemePieceImmersion`), compares the two presentations of its `i`-th piece
(`Stacks.Chow.zeroSchemeTestPieceIso`, `Stacks.Chow.zeroSchemePieceComparison`), decomposes its
Chow groups along the pieces (`Stacks.Chow.chowGroupZeroSchemePieceEquiv`), and proves that the
cap operation of a bivariant class commutes with restricting the test scheme along an open immersion
(`Stacks.Chow.BivariantClass.cap_chowGroupRestrict`).
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Zero schemes of pulled-back sections along an open immersion -/

/-- An isomorphism followed by an open immersion has the image of the immersion. This is
`AlgebraicGeometry.Scheme.Hom.opensRange_comp_of_isIso` read against a morphism presented by an
equality with the composite; `AlgebraicGeometry.Scheme.Hom.opensRange` carries an instance
argument, so the composite cannot be rewritten inside it. -/
theorem opensRange_eq_of_isIso_comp {A A' B : Scheme.{u}} (p : A ⟶ A') [IsIso p] (q : A' ⟶ B)
    [IsOpenImmersion q] (r : A ⟶ B) [IsOpenImmersion r] (h : p ≫ q = r) :
    r.opensRange = q.opensRange := by
  have hsurj : Function.Surjective p.base := fun y ↦
    ⟨(inv p).base y, by rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl⟩
  refine Opens.ext ?_
  simp only [Scheme.Hom.coe_opensRange]
  rw [← h, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr hsurj, Set.image_univ]

/-- Restriction of Chow classes along an isomorphism over the base is pushforward along an
inverse of it. This is `Stacks.Chow.chowGroupRestrict_of_isIso` with the inverse presented by the
identity it satisfies rather than as `CategoryTheory.inv`. -/
theorem chowGroupRestrict_eq_chowPushforwardOfIso_of_comp_id (C : ChowSituation.{u})
    {A B : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S)
    [LocallyOfFiniteType sB] (u : B ⟶ A) [IsIso u] (hu : u ≫ sA = sB) (v : A ⟶ B) [IsIso v]
    (hv : v ≫ sB = sA) (huv : u ≫ v = 𝟙 B) (k : ℤ) (α : chowGroup C sA k) :
    chowGroupRestrict C sA sB u hu k α = chowPushforwardOfIso C sA sB v hv k α := by
  rw [chowGroupRestrict_of_isIso C sA sB k u hu]
  exact chowPushforwardOfIso_congr_apply C sA sB (inv u) v (IsIso.inv_eq_of_hom_inv_id huv) _ hv
    k α

/-- A Chow class is the pushforward along an isomorphism over the base of its restriction along
that isomorphism. -/
theorem eq_chowPushforwardOfIso_chowGroupRestrict (C : ChowSituation.{u}) {A B : Scheme.{u}}
    (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB]
    (u : B ⟶ A) [IsIso u] (hu : u ≫ sA = sB) (k : ℤ) (α : chowGroup C sA k) :
    α = chowPushforwardOfIso C sB sA u hu k (chowGroupRestrict C sA sB u hu k α) := by
  rw [chowGroupRestrict_of_isIso C sA sB k u hu, chowPushforwardOfIso_comp_apply,
    chowPushforwardOfIso_congr_apply C sA sA (inv u ≫ u) (𝟙 A) (IsIso.inv_hom_id u) _
      (Category.id_comp sA) k, chowPushforwardOfIso_id]

/-- Pushing a Chow class forward along two isomorphisms over the base and then restricting along
a third is pushing it forward along the composite. This is the shape in which the Gysin axiom of
`Stacks.Chow.bivariantPieceAssemblyCap` compares the two sides on a piece. -/
theorem chowGroupRestrict_properChowPushforward_comp_of_isIso (C : ChowSituation.{u})
    {A B D E : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S)
    [LocallyOfFiniteType sB] (sD : D ⟶ C.S) [LocallyOfFiniteType sD] (sE : E ⟶ C.S)
    [LocallyOfFiniteType sE] (u : A ⟶ B) [IsIso u] (v : B ⟶ D) [IsIso v] (w : E ⟶ D) [IsIso w]
    (w' : D ⟶ E) [IsIso w'] (z : A ⟶ E) [IsIso z] (hu : u ≫ sB = sA) (hv : v ≫ sD = sB)
    (hw : w ≫ sD = sE) (hw' : w' ≫ sE = sD) (hz : z ≫ sE = sA) (hww' : w ≫ w' = 𝟙 E)
    (hcomp : u ≫ v ≫ w' = z) (k : ℤ)
    (hfu : ProperPushforwardFactorsThroughRationalEquivalence C sA sB u hu k)
    (hfv : ProperPushforwardFactorsThroughRationalEquivalence C sB sD v hv k)
    (hfz : ProperPushforwardFactorsThroughRationalEquivalence C sA sE z hz k)
    (α : chowGroup C sA k) :
    chowGroupRestrict C sD sE w hw k
        (properChowPushforward C sB sD v hv k hfv
          (properChowPushforward C sA sB u hu k hfu α)) =
      properChowPushforward C sA sE z hz k hfz α := by
  rw [properChowPushforward_eq_chowPushforwardOfIso C sA sB u hu k hfu,
    properChowPushforward_eq_chowPushforwardOfIso C sB sD v hv k hfv,
    properChowPushforward_eq_chowPushforwardOfIso C sA sE z hz k hfz,
    chowGroupRestrict_eq_chowPushforwardOfIso_of_comp_id C sD sE w hw w' hw' hww' k,
    chowPushforwardOfIso_comp_apply C sB sD sE v w' hv hw' k,
    chowPushforwardOfIso_comp_apply C sA sB sE u (v ≫ w') hu
      (by rw [Category.assoc, hw', hv]) k]
  exact chowPushforwardOfIso_congr_apply C sA sE (u ≫ v ≫ w') z hcomp _ hz k α

/-- Two open immersions into one scheme with the same image are isomorphic over it. This is
`AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq` read for images taken as open subschemes. -/
def isoOfOpensRangeEq {A B D : Scheme.{u}} (p : A ⟶ D) [IsOpenImmersion p] (q : B ⟶ D)
    [IsOpenImmersion q] (h : p.opensRange = q.opensRange) : A ≅ B :=
  IsOpenImmersion.isoOfRangeEq p q (by
    simpa only [Scheme.Hom.coe_opensRange] using
      congrArg (fun V : D.Opens ↦ (V : Set D)) h)

/-- The isomorphism of two open immersions with the same image lies over them. -/
@[reassoc (attr := simp)]
theorem isoOfOpensRangeEq_hom_fac {A B D : Scheme.{u}} (p : A ⟶ D) [IsOpenImmersion p]
    (q : B ⟶ D) [IsOpenImmersion q] (h : p.opensRange = q.opensRange) :
    (isoOfOpensRangeEq p q h).hom ≫ q = p :=
  IsOpenImmersion.isoOfRangeEq_hom_fac p q _

/-- The inverse of the isomorphism of two open immersions with the same image lies over them. -/
@[reassoc (attr := simp)]
theorem isoOfOpensRangeEq_inv_fac {A B D : Scheme.{u}} (p : A ⟶ D) [IsOpenImmersion p]
    (q : B ⟶ D) [IsOpenImmersion q] (h : p.opensRange = q.opensRange) :
    (isoOfOpensRangeEq p q h).inv ≫ p = q :=
  IsOpenImmersion.isoOfRangeEq_inv_fac p q _

/-- The image of the morphism of subschemes induced by an open immersion is the inverse image,
under the inclusion of the subscheme downstairs, of the image of the immersion: the morphism is
the base change of the open immersion along that inclusion. -/
theorem opensRange_comapSubschemeMap {A B : Scheme.{u}} (K : B.IdealSheafData) (u : A ⟶ B)
    [IsOpenImmersion u] :
    (comapSubschemeMap K u).opensRange = K.subschemeι ⁻¹ᵁ u.opensRange :=
  (opensRange_eq_of_isIso_comp (K.comapIso u).hom (pullback.snd u K.subschemeι)
      (comapSubschemeMap K u) rfl).trans
    (Scheme.Hom.opensRange_pullbackSnd u K.subschemeι)

/-- The image of an open immersion presented as an equality of ideal sheaves followed by the
morphism of subschemes induced by an open immersion `u` is the inverse image of the image of `u`. -/
private theorem opensRange_eqToHom_comp_comapSubschemeMap {A B : Scheme.{u}} (K : B.IdealSheafData)
    (u : A ⟶ B) [IsOpenImmersion u] {K' : A.IdealSheafData} (h : K' = K.comap u)
    (r : K'.subscheme ⟶ K.subscheme) [IsOpenImmersion r]
    (hr : r = eqToHom (congrArg Scheme.IdealSheafData.subscheme h) ≫ comapSubschemeMap K u) :
    r.opensRange = K.subschemeι ⁻¹ᵁ u.opensRange :=
  (opensRange_eq_of_isIso_comp _ (comapSubschemeMap K u) r hr.symm).trans
    (opensRange_comapSubschemeMap K u)

/-- The image of the open immersion of the zero scheme of a twice pulled-back section into the
zero scheme of the section pulled back once is the inverse image of the image of `u`. -/
theorem opensRange_zeroSchemeRestrictMap {A B T : Scheme.{u}} (qA : A ⟶ T) (qB : B ⟶ T)
    (u : A ⟶ B) [IsOpenImmersion u] (hu : u ≫ qB = qA) (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) :
    (zeroSchemeRestrictMap qA qB u hu L s).opensRange =
      (Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback qB).obj L)
        (AlgebraicGeometry.pullbackGlobalSections qB L s)).subschemeι ⁻¹ᵁ u.opensRange :=
  opensRange_eqToHom_comp_comapSubschemeMap _ u (zeroScheme_pullback_comap qA qB u hu L s) _ rfl

/-- **Stacks 0B6Y along an open immersion, with the module on the ambient scheme.** For an open
immersion `u : A ⟶ B` and an invertible module `L` on `B` with a global section `s`, the open
immersion of the zero scheme of the pulled-back section into the zero scheme of `s` itself. -/
def zeroSchemeOpensRestrictMap {A B : Scheme.{u}} (u : A ⟶ B) (L : B.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible B.sheaf.obj B.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) :
    (Stacks.Divisors.zeroScheme A ((Scheme.Modules.pullback u).obj L)
        (AlgebraicGeometry.pullbackGlobalSections u L s)).subscheme ⟶
      (Stacks.Divisors.zeroScheme B L s).subscheme :=
  eqToHom (congrArg Scheme.IdealSheafData.subscheme
      (Stacks.Divisors.zeroScheme_pullback u L s)) ≫
    comapSubschemeMap (Stacks.Divisors.zeroScheme B L s) u

/-- For an open immersion `u`, the map `zeroSchemeOpensRestrictMap u L s` is an open immersion. -/
instance isOpenImmersion_zeroSchemeOpensRestrictMap {A B : Scheme.{u}} (u : A ⟶ B)
    [IsOpenImmersion u] (L : B.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible B.sheaf.obj B.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) : IsOpenImmersion (zeroSchemeOpensRestrictMap u L s) :=
  inferInstanceAs (IsOpenImmersion (eqToHom _ ≫
    comapSubschemeMap (Stacks.Divisors.zeroScheme B L s) u))

/-- The open immersion of the zero scheme of a pulled-back section into the zero scheme of the
section lies over `u`. -/
theorem zeroSchemeOpensRestrictMap_comp_subschemeι {A B : Scheme.{u}} (u : A ⟶ B)
    (L : B.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible B.sheaf.obj B.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) :
    zeroSchemeOpensRestrictMap u L s ≫ (Stacks.Divisors.zeroScheme B L s).subschemeι =
      (Stacks.Divisors.zeroScheme A ((Scheme.Modules.pullback u).obj L)
        (AlgebraicGeometry.pullbackGlobalSections u L s)).subschemeι ≫ u := by
  rw [zeroSchemeOpensRestrictMap, Category.assoc, comapSubschemeMap_comp_subschemeι,
    ← Category.assoc, subschemeι_eqToHom (Stacks.Divisors.zeroScheme_pullback u L s)]

/-- The image of the open immersion of the zero scheme of a pulled-back section is the inverse
image of the image of `u` under the inclusion of the zero scheme downstairs. -/
theorem opensRange_zeroSchemeOpensRestrictMap {A B : Scheme.{u}} (u : A ⟶ B)
    [IsOpenImmersion u] (L : B.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible B.sheaf.obj B.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) :
    (zeroSchemeOpensRestrictMap u L s).opensRange =
      (Stacks.Divisors.zeroScheme B L s).subschemeι ⁻¹ᵁ u.opensRange :=
  opensRange_eqToHom_comp_comapSubschemeMap _ u (Stacks.Divisors.zeroScheme_pullback u L s) _ rfl

/-! ### The zero scheme of a pulled-back section decomposes along the pieces -/

section ZeroSchemePieces

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {I J : Type u} (UX : I → X.Opens) (UY : J → Y.Opens)
  (a : I → J) (ha : ∀ i, UX i ≤ f ⁻¹ᵁ UY (a i)) {T : Scheme.{u}} (g : T ⟶ Y) (L : T.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
  (s : Γ(L, ⊤))

/-- The projection of the `i`-th piece `X_i ×_{Y_{a(i)}} T_{a(i)}` of the base change `X ×_Y T`
to the test scheme `T`: the projection to the piece `T_{a(i)}` of the test scheme followed by its
inclusion. It is the composite of the `i`-th piece immersion with the projection of `X ×_Y T`, by
`Stacks.Chow.pieceImmersion_comp_snd`. -/
abbrev pieceTestProjection (i : I) :
    pullback (pieceMap f UX UY a ha i) (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl) ⟶ T :=
  pullback.snd (pieceMap f UX UY a ha i) (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl) ≫
    (g ⁻¹ᵁ UY (a i)).ι

/-- The zero scheme of the section pulled back to the `i`-th piece
`X_i ×_{Y_{a(i)}} T_{a(i)}` of the base change `X ×_Y T`. -/
abbrev zeroSchemePiece (i : I) :
    (pullback (pieceMap f UX UY a ha i)
      (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl)).IdealSheafData :=
  Stacks.Divisors.zeroScheme
    (pullback (pieceMap f UX UY a ha i) (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl))
    ((Scheme.Modules.pullback (pieceTestProjection f UX UY a ha g i)).obj L)
    (AlgebraicGeometry.pullbackGlobalSections (pieceTestProjection f UX UY a ha g i) L s)

/-- The open immersion cutting out the `i`-th piece of the zero scheme of the section pulled back
to `X ×_Y T`: the zero scheme of the section pulled back to the `i`-th piece of `X ×_Y T`. -/
def zeroSchemePieceImmersion (i : I) :
    (zeroSchemePiece f UX UY a ha g L s i).subscheme ⟶
      (Stacks.Divisors.zeroScheme (pullback f g)
        ((Scheme.Modules.pullback (pullback.snd f g)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd f g) L s)).subscheme :=
  zeroSchemeRestrictMap (pieceTestProjection f UX UY a ha g i) (pullback.snd f g)
    (pieceImmersion f UX UY a ha g i) (pieceImmersion_comp_snd f UX UY a ha g i) L s

/-- The map `zeroSchemePieceImmersion` is an open immersion. -/
instance isOpenImmersion_zeroSchemePieceImmersion (i : I) :
    IsOpenImmersion (zeroSchemePieceImmersion f UX UY a ha g L s i) := by
  rw [zeroSchemePieceImmersion]; infer_instance

/-- The `i`-th piece of the zero scheme lies over the `i`-th piece of `X ×_Y T`. -/
theorem zeroSchemePieceImmersion_comp_subschemeι (i : I) :
    zeroSchemePieceImmersion f UX UY a ha g L s i ≫
        (Stacks.Divisors.zeroScheme (pullback f g)
          ((Scheme.Modules.pullback (pullback.snd f g)).obj L)
          (AlgebraicGeometry.pullbackGlobalSections (pullback.snd f g) L s)).subschemeι =
      (zeroSchemePiece f UX UY a ha g L s i).subschemeι ≫ pieceImmersion f UX UY a ha g i :=
  zeroSchemeRestrictMap_comp_subschemeι (pieceTestProjection f UX UY a ha g i)
    (pullback.snd f g) (pieceImmersion f UX UY a ha g i)
    (pieceImmersion_comp_snd f UX UY a ha g i) L s

/-- The image of the `i`-th piece of the zero scheme is the inverse image of the preimage of the
piece `X_i`. -/
theorem opensRange_zeroSchemePieceImmersion (i : I) :
    (zeroSchemePieceImmersion f UX UY a ha g L s i).opensRange =
      (Stacks.Divisors.zeroScheme (pullback f g)
          ((Scheme.Modules.pullback (pullback.snd f g)).obj L)
          (AlgebraicGeometry.pullbackGlobalSections (pullback.snd f g) L s)).subschemeι ⁻¹ᵁ
        (pullback.fst f g ⁻¹ᵁ UX i) := by
  have h := opensRange_zeroSchemeRestrictMap (pieceTestProjection f UX UY a ha g i)
    (pullback.snd f g) (pieceImmersion f UX UY a ha g i)
    (pieceImmersion_comp_snd f UX UY a ha g i) L s
  rw [opensRange_pieceImmersion] at h
  exact h

/-- The pieces of the zero scheme of the pulled-back section decompose it into open and closed
subschemes: they are the inverse images of the pieces of `X ×_Y T`, which in turn are the
preimages of the pieces of `X`. -/
theorem isClopenDecomposition_opensRange_zeroSchemePieceImmersion
    (hX : IsClopenDecomposition UX) :
    IsClopenDecomposition
      fun i ↦ (zeroSchemePieceImmersion f UX UY a ha g L s i).opensRange := by
  simp only [opensRange_zeroSchemePieceImmersion]
  exact (hX.preimage (pullback.fst f g)).preimage
    (Stacks.Divisors.zeroScheme (pullback f g)
      ((Scheme.Modules.pullback (pullback.snd f g)).obj L)
      (AlgebraicGeometry.pullbackGlobalSections (pullback.snd f g) L s)).subschemeι

/-! ### The pieces of the zero scheme on the test scheme -/

/-- The zero scheme of the section restricted to the piece `T_{a(i)} = g^{-1}(Y_{a(i)})` of the
test scheme. It is the test scheme at which the Gysin axiom of the class `c_i` on the `i`-th piece
is read. -/
abbrev zeroSchemeTestPiece (i : I) : ((g ⁻¹ᵁ UY (a i) : Scheme.{u})).IdealSheafData :=
  Stacks.Divisors.zeroScheme ((g ⁻¹ᵁ UY (a i) : Scheme.{u}))
    ((Scheme.Modules.pullback (g ⁻¹ᵁ UY (a i)).ι).obj L)
    (AlgebraicGeometry.pullbackGlobalSections (g ⁻¹ᵁ UY (a i)).ι L s)

/-- The two presentations of the `i`-th piece of the zero scheme `Z(s) ⊆ T` agree: the open
subscheme of `Z(s)` lying over `Y_{a(i)}` is the zero scheme of the section restricted to
`T_{a(i)}`, the two open immersions into `Z(s)` having the same image. -/
def zeroSchemeTestPieceIso (i : I) :
    ((((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ⁻¹ᵁ UY (a i) : Scheme.{u})) ≅
      (zeroSchemeTestPiece UY a g L s i).subscheme :=
  isoOfOpensRangeEq (((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ⁻¹ᵁ UY (a i)).ι
    (zeroSchemeOpensRestrictMap (g ⁻¹ᵁ UY (a i)).ι L s) (by
      rw [Scheme.Opens.opensRange_ι, opensRange_zeroSchemeOpensRestrictMap,
        Scheme.Opens.opensRange_ι]
      exact Scheme.Hom.comp_preimage _ _ _)

/-- The comparison of the two presentations of the `i`-th piece of `Z(s)` lies over `Z(s)`. -/
@[reassoc]
theorem zeroSchemeTestPieceIso_hom_comp (i : I) :
    (zeroSchemeTestPieceIso UY a g L s i).hom ≫
        zeroSchemeOpensRestrictMap (g ⁻¹ᵁ UY (a i)).ι L s =
      (((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ⁻¹ᵁ UY (a i)).ι :=
  isoOfOpensRangeEq_hom_fac _ _ _

/-- The comparison of the two presentations of the `i`-th piece of `Z(s)` lies over the test
scheme `T`. -/
@[reassoc]
theorem zeroSchemeTestPieceIso_hom_comp_subschemeι (i : I) :
    (zeroSchemeTestPieceIso UY a g L s i).hom ≫
        ((zeroSchemeTestPiece UY a g L s i).subschemeι ≫ (g ⁻¹ᵁ UY (a i)).ι) =
      (((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ⁻¹ᵁ UY (a i)).ι ≫
        (Stacks.Divisors.zeroScheme T L s).subschemeι := by
  rw [← zeroSchemeOpensRestrictMap_comp_subschemeι (g ⁻¹ᵁ UY (a i)).ι L s, ← Category.assoc,
    zeroSchemeTestPieceIso_hom_comp]

/-- The comparison of the two presentations of the `i`-th piece of `Z(s)` lies over
`Y_{a(i)}`. -/
@[reassoc]
theorem zeroSchemeTestPieceIso_hom_comp_resLE (i : I) :
    (zeroSchemeTestPieceIso UY a g L s i).hom ≫
        ((zeroSchemeTestPiece UY a g L s i).subschemeι ≫
          g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl) =
      ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g).resLE (UY (a i))
        (((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ⁻¹ᵁ UY (a i)) le_rfl := by
  rw [← cancel_mono (UY (a i)).ι]
  simp only [Category.assoc, Scheme.Hom.resLE_comp_ι]
  rw [zeroSchemeTestPieceIso_hom_comp_subschemeι_assoc]

/-- The inverse comparison of the two presentations of the `i`-th piece of `Z(s)` lies over
`Y_{a(i)}`. -/
@[reassoc]
theorem zeroSchemeTestPieceIso_inv_comp_resLE (i : I) :
    (zeroSchemeTestPieceIso UY a g L s i).inv ≫
        ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g).resLE (UY (a i))
          (((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ⁻¹ᵁ UY (a i)) le_rfl =
      (zeroSchemeTestPiece UY a g L s i).subschemeι ≫
        g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl := by
  rw [Iso.inv_comp_eq]
  exact (zeroSchemeTestPieceIso_hom_comp_resLE UY a g L s i).symm

/-- The comparison of the two base changes of `f_i` along the two presentations of the `i`-th
piece of the zero scheme `Z(s)` on the test scheme. -/
def zeroSchemeTestPieceBaseChange (i : I) :
    pullback (pieceMap f UX UY a ha i)
        (((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g).resLE (UY (a i))
          (((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ⁻¹ᵁ UY (a i)) le_rfl) ⟶
      pullback (pieceMap f UX UY a ha i)
        ((zeroSchemeTestPiece UY a g L s i).subschemeι ≫
          g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl) :=
  pullback.lift
    (pullback.fst (pieceMap f UX UY a ha i)
      (((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g).resLE (UY (a i))
        (((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ⁻¹ᵁ UY (a i)) le_rfl))
    (pullback.snd (pieceMap f UX UY a ha i)
        (((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g).resLE (UY (a i))
          (((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ⁻¹ᵁ UY (a i)) le_rfl) ≫
      (zeroSchemeTestPieceIso UY a g L s i).hom)
    (by rw [Category.assoc, zeroSchemeTestPieceIso_hom_comp_resLE, pullback.condition])

/-- The comparison of the two base changes is compatible with the projections to `X_i`. -/
@[reassoc (attr := simp)]
theorem zeroSchemeTestPieceBaseChange_fst (i : I) :
    zeroSchemeTestPieceBaseChange f UX UY a ha g L s i ≫
        pullback.fst (pieceMap f UX UY a ha i)
          ((zeroSchemeTestPiece UY a g L s i).subschemeι ≫
            g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl) =
      pullback.fst (pieceMap f UX UY a ha i)
        (((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g).resLE (UY (a i))
          (((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ⁻¹ᵁ UY (a i)) le_rfl) :=
  pullback.lift_fst _ _ _

/-- The comparison of the two base changes is compatible with the projections to the two
presentations of the `i`-th piece of `Z(s)`. -/
@[reassoc (attr := simp)]
theorem zeroSchemeTestPieceBaseChange_snd (i : I) :
    zeroSchemeTestPieceBaseChange f UX UY a ha g L s i ≫
        pullback.snd (pieceMap f UX UY a ha i)
          ((zeroSchemeTestPiece UY a g L s i).subschemeι ≫
            g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl) =
      pullback.snd (pieceMap f UX UY a ha i)
          (((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g).resLE (UY (a i))
            (((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ⁻¹ᵁ UY (a i)) le_rfl) ≫
        (zeroSchemeTestPieceIso UY a g L s i).hom :=
  pullback.lift_snd _ _ _

/-- The comparison `zeroSchemeTestPieceBaseChange` of the two base changes is an isomorphism. -/
instance isIso_zeroSchemeTestPieceBaseChange (i : I) :
    IsIso (zeroSchemeTestPieceBaseChange f UX UY a ha g L s i) := by
  refine ⟨⟨pullback.lift
    (pullback.fst (pieceMap f UX UY a ha i)
      ((zeroSchemeTestPiece UY a g L s i).subschemeι ≫
        g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl))
    (pullback.snd (pieceMap f UX UY a ha i)
        ((zeroSchemeTestPiece UY a g L s i).subschemeι ≫
          g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl) ≫
      (zeroSchemeTestPieceIso UY a g L s i).inv)
    (by rw [Category.assoc, zeroSchemeTestPieceIso_inv_comp_resLE, pullback.condition]),
    ?_, ?_⟩⟩
  · refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, zeroSchemeTestPieceBaseChange_fst,
        Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc,
        zeroSchemeTestPieceBaseChange_snd, Category.assoc, Iso.hom_inv_id, Category.comp_id,
        Category.id_comp]
  · refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, zeroSchemeTestPieceBaseChange_fst, pullback.lift_fst,
        Category.id_comp]
    · rw [Category.assoc, zeroSchemeTestPieceBaseChange_snd, ← Category.assoc,
        pullback.lift_snd, Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]

/-- Pulling the section back to the `i`-th piece of `X ×_Y T` in two steps — first to the piece
`T_{a(i)}` of the test scheme, then to the piece of `X ×_Y T` — gives the same zero scheme as
pulling it back along the composite projection. -/
theorem zeroScheme_pieceTestProjection (i : I) :
    Stacks.Divisors.zeroScheme
        (pullback (pieceMap f UX UY a ha i) (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl))
        ((Scheme.Modules.pullback (pullback.snd (pieceMap f UX UY a ha i)
            (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl))).obj
          ((Scheme.Modules.pullback (g ⁻¹ᵁ UY (a i)).ι).obj L))
        (AlgebraicGeometry.pullbackGlobalSections
          (pullback.snd (pieceMap f UX UY a ha i)
            (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl))
          ((Scheme.Modules.pullback (g ⁻¹ᵁ UY (a i)).ι).obj L)
          (AlgebraicGeometry.pullbackGlobalSections (g ⁻¹ᵁ UY (a i)).ι L s)) =
      zeroSchemePiece f UX UY a ha g L s i :=
  zeroScheme_pullback_pullback _ _ L s

/-- **Stacks 0B6Y for the `i`-th piece.** The base change of `f_i` along the `i`-th piece of the
zero scheme `Z(s)` on the test scheme is the `i`-th piece of the zero scheme of the section
pulled back to `X ×_Y T`; the two zero schemes on that piece are literally equal, by
`Stacks.Chow.zeroScheme_pullback_pullback`. -/
def zeroSchemePieceIso (i : I) :
    pullback (pieceMap f UX UY a ha i)
        ((zeroSchemeTestPiece UY a g L s i).subschemeι ≫
          g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl) ≅
      (zeroSchemePiece f UX UY a ha g L s i).subscheme :=
  (zeroSchemeBaseChangeIso (pieceMap f UX UY a ha i)
      (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl)
      ((Scheme.Modules.pullback (g ⁻¹ᵁ UY (a i)).ι).obj L)
      (AlgebraicGeometry.pullbackGlobalSections (g ⁻¹ᵁ UY (a i)).ι L s)).trans
    (eqToIso (congrArg Scheme.IdealSheafData.subscheme
      (zeroScheme_pieceTestProjection f UX UY a ha g L s i)))

/-- The identification of the `i`-th piece of the zero scheme lies over the canonical map of the
two base changes of `f_i`. -/
@[reassoc]
theorem zeroSchemePieceIso_hom_comp_subschemeι (i : I) :
    (zeroSchemePieceIso f UX UY a ha g L s i).hom ≫
        (zeroSchemePiece f UX UY a ha g L s i).subschemeι =
      bivariantBaseChangeMap (pieceMap f UX UY a ha i)
        (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl)
        (zeroSchemeTestPiece UY a g L s i).subschemeι := by
  rw [zeroSchemePieceIso, Iso.trans_hom, eqToIso.hom, Category.assoc,
    subschemeι_eqToHom (zeroScheme_pieceTestProjection f UX UY a ha g L s i),
    zeroSchemeBaseChangeIso_hom_subschemeι]

/-- The `i`-th piece of the zero scheme of the section pulled back to `X ×_Y T`, identified with
the base change of `f_i` along the `i`-th piece of the zero scheme `Z(s)` read as an open
subscheme of `Z(s)`. -/
def zeroSchemePieceComparison (i : I) :
    pullback (pieceMap f UX UY a ha i)
        (((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g).resLE (UY (a i))
          (((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) ⁻¹ᵁ UY (a i)) le_rfl) ≅
      (zeroSchemePiece f UX UY a ha g L s i).subscheme :=
  (asIso (zeroSchemeTestPieceBaseChange f UX UY a ha g L s i)).trans
    (zeroSchemePieceIso f UX UY a ha g L s i)

/-- The identification of the `i`-th piece of the zero scheme on `X ×_Y T` lies over the
canonical map of the two base changes of `f`: it is the restriction to the `i`-th pieces of the
identification `Stacks.Chow.zeroSchemeBaseChangeIso` downstairs. -/
theorem zeroSchemePieceComparison_hom_comp (i : I) :
    (zeroSchemePieceComparison f UX UY a ha g L s i).hom ≫
        (zeroSchemePieceImmersion f UX UY a ha g L s i ≫
          (Stacks.Divisors.zeroScheme (pullback f g)
            ((Scheme.Modules.pullback (pullback.snd f g)).obj L)
            (AlgebraicGeometry.pullbackGlobalSections (pullback.snd f g) L s)).subschemeι) =
      pieceImmersion f UX UY a ha ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ g) i ≫
        bivariantBaseChangeMap f g (Stacks.Divisors.zeroScheme T L s).subschemeι := by
  have h1 : (zeroSchemePieceComparison f UX UY a ha g L s i).hom ≫
      (zeroSchemePiece f UX UY a ha g L s i).subschemeι =
        zeroSchemeTestPieceBaseChange f UX UY a ha g L s i ≫
          bivariantBaseChangeMap (pieceMap f UX UY a ha i)
            (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl)
            (zeroSchemeTestPiece UY a g L s i).subschemeι := by
    rw [zeroSchemePieceComparison, Iso.trans_hom, asIso_hom, Category.assoc,
      zeroSchemePieceIso_hom_comp_subschemeι]
  rw [zeroSchemePieceImmersion_comp_subschemeι, ← Category.assoc, h1, Category.assoc]
  refine pullback.hom_ext ?_ ?_
  · simp only [Category.assoc, pieceImmersion_comp_fst, pullbackMap_fst, pullbackMap_fst_assoc,
      Category.comp_id, Category.id_comp, zeroSchemeTestPieceBaseChange_fst_assoc]
  · simp only [Category.assoc, pieceImmersion_comp_snd, pieceImmersion_comp_snd_assoc,
      pullbackMap_snd, pullbackMap_snd_assoc, zeroSchemeTestPieceBaseChange_snd_assoc,
      zeroSchemeTestPieceIso_hom_comp_subschemeι]

end ZeroSchemePieces

/-! ### The Chow groups of that zero scheme decompose along the pieces -/

section ZeroSchemeChowPieces

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (f : X ⟶ Y) {I J : Type u} (UX : I → X.Opens) (UY : J → Y.Opens) (a : I → J)
  (ha : ∀ i, UX i ≤ f ⁻¹ᵁ UY (a i)) (hX : IsClopenDecomposition UX) {T : Scheme.{u}} (g : T ⟶ Y)
  [LocallyOfFiniteType g] (L : T.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
  (s : Γ(L, ⊤))

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType g] in
/-- The `i`-th piece of the zero scheme is a scheme over the base, its structure morphism being
read through the inclusion into the `i`-th piece of `X ×_Y T`. -/
theorem zeroSchemePieceImmersion_comp_structureMorphism (i : I) :
    zeroSchemePieceImmersion f UX UY a ha g L s i ≫
        ((Stacks.Divisors.zeroScheme (pullback f g)
            ((Scheme.Modules.pullback (pullback.snd f g)).obj L)
            (AlgebraicGeometry.pullbackGlobalSections (pullback.snd f g) L s)).subschemeι ≫
          (pullback.fst f g ≫ sX)) =
      (zeroSchemePiece f UX UY a ha g L s i).subschemeι ≫
        (pullback.fst (pieceMap f UX UY a ha i)
          (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl) ≫ ((UX i).ι ≫ sX)) := by
  rw [← Category.assoc, zeroSchemePieceImmersion_comp_subschemeι, Category.assoc,
    pieceImmersion_comp_structureMorphism]

/-- **`CH_k(Z(s')) = ∏_i CH_k(Z(s'_i))`.** The Chow groups of the zero scheme of the section
pulled back to `X ×_Y T` decompose along the pieces of the decomposition of `X`, the components
being restriction of Chow classes along the inclusions of the pieces of the zero scheme.

This is `Stacks.Chow.chowGroupClopenRestrictEquiv` for the decomposition supplied by
`Stacks.Chow.isClopenDecomposition_opensRange_zeroSchemePieceImmersion`. -/
def chowGroupZeroSchemePieceEquiv (k : ℤ) :
    chowGroup C ((Stacks.Divisors.zeroScheme (pullback f g)
        ((Scheme.Modules.pullback (pullback.snd f g)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd f g) L s)).subschemeι ≫
      (pullback.fst f g ≫ sX)) k ≃+
      ∀ i, chowGroup C ((zeroSchemePiece f UX UY a ha g L s i).subschemeι ≫
        (pullback.fst (pieceMap f UX UY a ha i)
          (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl) ≫ ((UX i).ι ≫ sX))) k :=
  chowGroupClopenRestrictEquiv C _
    (fun i ↦ (zeroSchemePiece f UX UY a ha g L s i).subschemeι ≫
      (pullback.fst (pieceMap f UX UY a ha i)
        (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl) ≫ ((UX i).ι ≫ sX)))
    (fun i ↦ zeroSchemePieceImmersion f UX UY a ha g L s i)
    (fun i ↦ zeroSchemePieceImmersion_comp_structureMorphism C sX f UX UY a ha g L s i)
    (isClopenDecomposition_opensRange_zeroSchemePieceImmersion f UX UY a ha g L s hX) k

/-- The components of that product decomposition are restriction of Chow classes along the
inclusions of the pieces of the zero scheme. -/
@[simp]
theorem chowGroupZeroSchemePieceEquiv_apply (k : ℤ)
    (α : chowGroup C ((Stacks.Divisors.zeroScheme (pullback f g)
        ((Scheme.Modules.pullback (pullback.snd f g)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd f g) L s)).subschemeι ≫
      (pullback.fst f g ≫ sX)) k) (i : I) :
    chowGroupZeroSchemePieceEquiv C sX f UX UY a ha hX g L s k α i =
      chowGroupRestrict C ((Stacks.Divisors.zeroScheme (pullback f g)
          ((Scheme.Modules.pullback (pullback.snd f g)).obj L)
          (AlgebraicGeometry.pullbackGlobalSections (pullback.snd f g) L s)).subschemeι ≫
        (pullback.fst f g ≫ sX))
        ((zeroSchemePiece f UX UY a ha g L s i).subschemeι ≫
          (pullback.fst (pieceMap f UX UY a ha i)
            (g.resLE (UY (a i)) (g ⁻¹ᵁ UY (a i)) le_rfl) ≫ ((UX i).ι ≫ sX)))
        (zeroSchemePieceImmersion f UX UY a ha g L s i)
        (zeroSchemePieceImmersion_comp_structureMorphism C sX f UX UY a ha g L s i) k α :=
  chowGroupClopenRestrictEquiv_apply C _ _ _ _ _ k α i

end ZeroSchemeChowPieces

/-- Restriction of Chow classes along an open immersion over the base is unchanged by replacing
the structure morphism of the target with an equal one. -/
theorem chowGroupCongr_chowGroupRestrict (C : ChowSituation.{u}) {Z W : Scheme.{u}}
    (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (sW sW' : W ⟶ C.S) [LocallyOfFiniteType sW]
    [LocallyOfFiniteType sW'] (v : W ⟶ Z) [IsOpenImmersion v] (hv : v ≫ sZ = sW)
    (hv' : v ≫ sZ = sW') (h : sW = sW') (k : ℤ) (α : chowGroup C sZ k) :
    chowGroupCongr C h k (chowGroupRestrict C sZ sW v hv k α) =
      chowGroupRestrict C sZ sW' v hv' k α := by
  cases h
  rfl

/-- Restriction of Chow classes along an open immersion over the base is unchanged by replacing
the structure morphism of the source with an equal one. -/
theorem chowGroupRestrict_chowGroupCongr (C : ChowSituation.{u}) {Z W : Scheme.{u}}
    (sZ sZ' : Z ⟶ C.S) [LocallyOfFiniteType sZ] [LocallyOfFiniteType sZ'] (sW : W ⟶ C.S)
    [LocallyOfFiniteType sW] (v : W ⟶ Z) [IsOpenImmersion v] (hv : v ≫ sZ = sW)
    (hv' : v ≫ sZ' = sW) (h : sZ = sZ') (k : ℤ) (α : chowGroup C sZ k) :
    chowGroupRestrict C sZ' sW v hv' k (chowGroupCongr C h k α) =
      chowGroupRestrict C sZ sW v hv k α := by
  cases h
  rfl

/-! ### Restriction of the test scheme along an open immersion -/

/-- Restriction of Chow classes along an open immersion over the base is flat pullback in relative
dimension zero: the two agree up to the transport of the degree from `k` to `k + 0`. On cycles
this is `Stacks.Chow.cycleGroupRestrict_eq_flatPullback`. -/
theorem heq_chowGroupRestrict_flatPullbackChow (C : ChowSituation.{u}) {Z W : Scheme.{u}}
    (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (sW : W ⟶ C.S) [LocallyOfFiniteType sW]
    (v : W ⟶ Z) [IsOpenImmersion v] (hv : v ≫ sZ = sW)
    (hr : AlgebraicGeometry.RelativeDimension v 0) (k : ℤ)
    (hfac : FlatPullbackFactorsThroughRationalEquivalence C sW sZ v hv 0 hr k)
    (α : chowGroup C sZ k) :
    HEq (chowGroupRestrict C sZ sW v hv k α)
      (flatPullbackChow C sW sZ v hv 0 hr k hfac α) := by
  have key : ∀ (n : ℤ), k = n → ∀ (x : CycleGroup C sW k) (y : CycleGroup C sW n),
      x.1 = y.1 → HEq (QuotientAddGroup.mk' (rationalEquivalences C sW k) x)
        (QuotientAddGroup.mk' (rationalEquivalences C sW n) y) := by
    intro n hn x y h
    cases hn
    exact heq_of_eq (congrArg (QuotientAddGroup.mk' (rationalEquivalences C sW k))
      (Subtype.ext h))
  induction α using QuotientAddGroup.induction_on with
  | H c =>
    exact key (k + ((0 : ℕ) : ℤ)) (by simp) (cycleGroupRestrict C sZ sW v hv k c)
      (flatPullback C sW sZ v hv 0 hr k c)
      (cycleGroupRestrict_eq_flatPullback C sZ sW v hv hr k c)

section CapRestrict

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y)
  [LocallyOfFiniteType f] (hf : f ≫ sY = sX) (p : ℤ)

/-- The cap operations of a bivariant class at two degrees are carried to one another by a
heterogeneous equality of classes. -/
theorem heq_cap_of_heq (c : BivariantClass C G sX sY f hf p) {T : Scheme.{u}} (g : T ⟶ Y)
    [LocallyOfFiniteType g] {k l : ℤ} (hkl : k = l) {x : chowGroup C (g ≫ sY) k}
    {y : chowGroup C (g ≫ sY) l} (hxy : HEq x y) : HEq (c.cap g k x) (c.cap g l y) := by
  cases hkl
  exact heq_of_eq (congrArg (c.cap g k) (eq_of_heq hxy))

/-- **The cap operation of a bivariant class commutes with restricting the test scheme along an
open immersion.** This is the flat-pullback axiom of Stacks 0B76 in relative dimension zero, where
flat pullback is restriction of Chow classes; it carries no hypothesis, because Stacks 02S1 along
an open immersion is `Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_of_isOpenImmersion`
and needs none. -/
theorem BivariantClass.cap_chowGroupRestrict (c : BivariantClass C G sX sY f hf p)
    {T T' : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (v : T' ⟶ T) [IsOpenImmersion v]
    (m : T' ⟶ Y) [LocallyOfFiniteType m] (hm : v ≫ g = m)
    (v' : pullback f m ⟶ pullback f g) [IsOpenImmersion v']
    (sq : IsPullback (pullback.snd f m) v' v (pullback.snd f g))
    (hfst : v' ≫ pullback.fst f g = pullback.fst f m) (k : ℤ)
    (hvY : v ≫ (g ≫ sY) = m ≫ sY)
    (hbase : v' ≫ (pullback.fst f g ≫ sX) = pullback.fst f m ≫ sX)
    (α : chowGroup C (g ≫ sY) k) :
    chowGroupRestrict C (pullback.fst f g ≫ sX) (pullback.fst f m ≫ sX) v' hbase (k - p)
        (c.cap g k α) =
      c.cap m k (chowGroupRestrict C (g ≫ sY) (m ≫ sY) v hvY k α) := by
  have hr : AlgebraicGeometry.RelativeDimension v 0 :=
    relativeDimension_of_isOpenImmersion v
  have hr' : AlgebraicGeometry.RelativeDimension v' 0 :=
    relativeDimension_of_isOpenImmersion v'
  have hfacv := flatPullbackFactorsThroughRationalEquivalence_of_isOpenImmersion C (g ≫ sY)
    (m ≫ sY) v hvY k
  have hfacv' := flatPullbackFactorsThroughRationalEquivalence_of_isOpenImmersion C
    (pullback.fst f g ≫ sX) (pullback.fst f m ≫ sX) v' hbase (k - p)
  refine eq_of_heq (((heq_chowGroupRestrict_flatPullbackChow C (pullback.fst f g ≫ sX)
      (pullback.fst f m ≫ sX) v' hbase hr' (k - p) hfacv' (c.cap g k α)).trans
    ((BivariantClass.flat_naturality_of_eq C G sX sY f hf p c g v m hm 0 hr v' sq hfst k hvY hr'
      hfacv hfacv' α).symm.trans ?_)))
  exact heq_cap_of_heq C G sX sY f hf p c m (by simp)
    (heq_chowGroupRestrict_flatPullbackChow C (g ≫ sY) (m ≫ sY) v hvY hr k hfacv α).symm

end CapRestrict

end Stacks.Chow

end
