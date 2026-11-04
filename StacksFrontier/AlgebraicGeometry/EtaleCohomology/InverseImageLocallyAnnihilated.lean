module

public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Sites.Pullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.IntegralQuasiFinitePushforward
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.PrimaryVanishing
public import StacksFrontier.CategoryTheory.Triangulated.BrownRepresentability

/-!
# Local annihilation of sections under inverse image and along integral direct images

An abelian sheaf `F` on a site is *locally annihilated along* a predicate `P` on the natural
numbers (`Stacks.EtaleCohomology.LocallyAnnihilated`) if every local section is, locally, killed
by an integer satisfying `P`. With `P n ↔ n` a positive power of `p` this is being `p`-power
torsion, with `P n ↔ n > 0` prime to `p` it is being torsion prime to `p`.

This file proves that, for a predicate closed under products and satisfied by some integer, the
condition is preserved by the inverse image of sheaves along a continuous functor (constructed as
a pointwise left Kan extension followed by sheafification), and passes to quotient sheaves. For a
morphism of schemes `f : X ⟶ Y` which is integral, the counit `f⁻¹ f_* F ⟶ F` of the étale
inverse-image/direct-image adjunction is surjective (Tag 04C9), so `F` is locally annihilated
along `P` as soon as `f_* F` is. This is how the torsion side conditions of the statements of
Situation 0A52 move from `f_* F` back to `F` in Lemma 0A5D.

## Main definitions

* `Stacks.EtaleCohomology.annihilatorSieve`: the sieve of arrows along which a section of a
  presheaf of abelian groups is killed by an integer satisfying `P`.

## Main results

* `Stacks.EtaleCohomology.annihilatorSieve_mem_leftKanExtension`: local annihilation passes to
  a pointwise left Kan extension along a cover-preserving functor.
* `Stacks.EtaleCohomology.locallyAnnihilated_sheafPullbackConstruction`: it passes to the inverse
  image of sheaves.
* `Stacks.EtaleCohomology.LocallyAnnihilated.of_epi`: it passes to quotient sheaves.
* `Stacks.EtaleCohomology.locallyAnnihilated_of_directImage_of_isIntegralHom`: for `f` integral,
  it passes from `f_* F` to `F`; `Stacks.EtaleCohomology.isPrimePowerTorsion_of_directImage` and
  `Stacks.EtaleCohomology.isPrimeToCharacteristicTorsion_of_directImage` are the two torsion
  conditions of Situation 0A52.

## References

* [Stacks Project, Tag 04C9](https://stacks.math.columbia.edu/tag/04C9)
* [Stacks Project, Tag 0A5D](https://stacks.math.columbia.edu/tag/0A5D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe w v₁ v₂ u₁ u₂ u v

namespace Stacks.EtaleCohomology

section Presheaf

variable {C : Type u₁} [Category.{v₁} C] (P : ℕ → Prop) (Q : Cᵒᵖ ⥤ AddCommGrpCat.{w})

/-- **The annihilator sieve of a section.** For a section `x` of a presheaf of abelian groups over
`U`, the sieve of arrows `V ⟶ U` along which the restriction of `x` is killed by an integer
satisfying `P`. -/
def annihilatorSieve {U : C} (x : Q.obj (op U)) : Sieve U where
  arrows V f := ∃ n : ℕ, P n ∧ n • Q.map f.op x = 0
  downward_closed := by
    rintro V W f ⟨n, hn, h⟩ g
    refine ⟨n, hn, ?_⟩
    have e : Q.map (g ≫ f).op x = Q.map g.op (Q.map f.op x) := by simp
    rw [e, ← map_nsmul, h, map_zero]

variable {P Q}

/-- An arrow `f : V ⟶ U` lies in the annihilator sieve of `x` if and only if some integer `n`
satisfying `P` kills the restriction of `x` along `f`. -/
@[simp]
theorem annihilatorSieve_apply {U V : C} (x : Q.obj (op U)) (f : V ⟶ U) :
    annihilatorSieve P Q x f ↔ ∃ n : ℕ, P n ∧ n • Q.map f.op x = 0 :=
  Iff.rfl

/-- The annihilator sieve of a restriction is the pullback of the annihilator sieve. -/
theorem annihilatorSieve_pullback {U V : C} (x : Q.obj (op U)) (g : V ⟶ U) :
    (annihilatorSieve P Q x).pullback g = annihilatorSieve P Q (Q.map g.op x) := by
  ext W h
  have e : Q.map (h ≫ g).op x = Q.map h.op (Q.map g.op x) := by simp
  simp only [Sieve.pullback_apply, annihilatorSieve_apply, e]

/-- The zero section is annihilated everywhere, as soon as some integer satisfies `P`. -/
theorem annihilatorSieve_zero (hP : ∃ n, P n) (U : C) :
    annihilatorSieve P Q (0 : Q.obj (op U)) = ⊤ :=
  top_unique fun _ _ _ ↦ ⟨hP.choose, hP.choose_spec, by simp⟩

/-- A sum of two sections is annihilated where both are, if `P` is closed under products. -/
theorem annihilatorSieve_add (hmul : ∀ m n, P m → P n → P (m * n)) {U : C}
    (x y : Q.obj (op U)) :
    annihilatorSieve P Q x ⊓ annihilatorSieve P Q y ≤ annihilatorSieve P Q (x + y) := by
  rintro V f ⟨⟨m, hm, hx⟩, ⟨n, hn, hy⟩⟩
  refine ⟨m * n, hmul m n hm hn, ?_⟩
  have h₁ : (m * n) • Q.map f.op x = 0 := by rw [mul_comm, mul_smul, hx, smul_zero]
  have h₂ : (m * n) • Q.map f.op y = 0 := by rw [mul_smul, hy, smul_zero]
  rw [map_add, smul_add, h₁, h₂, add_zero]

/-- The negative of a section is annihilated where the section is. -/
theorem annihilatorSieve_neg {U : C} (x : Q.obj (op U)) :
    annihilatorSieve P Q x ≤ annihilatorSieve P Q (-x) := by
  rintro V f ⟨n, hn, hx⟩
  exact ⟨n, hn, by rw [map_neg, smul_neg, hx, neg_zero]⟩

variable (J : GrothendieckTopology C)

/-- **The locally annihilated sections form a subgroup**, for `P` closed under products and
satisfied by some integer. -/
def locallyAnnihilatedSubgroup (hP : ∃ n, P n) (hmul : ∀ m n, P m → P n → P (m * n)) (U : C) :
    AddSubgroup (Q.obj (op U)) where
  carrier := {x | annihilatorSieve P Q x ∈ J U}
  zero_mem' := by
    rw [Set.mem_setOf_eq, annihilatorSieve_zero hP]
    exact J.top_mem U
  add_mem' hx hy := J.superset_covering (annihilatorSieve_add hmul _ _)
    (J.intersection_covering hx hy)
  neg_mem' hx := J.superset_covering (annihilatorSieve_neg _) hx

variable {J}

/-- **Local annihilation passes along a locally surjective map of presheaves.** -/
theorem annihilatorSieve_mem_of_isLocallySurjective {Q₁ Q₂ : Cᵒᵖ ⥤ AddCommGrpCat.{w}}
    (η : Q₁ ⟶ Q₂) [Presheaf.IsLocallySurjective J η]
    (h : ∀ (U : C) (x : Q₁.obj (op U)), annihilatorSieve P Q₁ x ∈ J U) (U : C)
    (y : Q₂.obj (op U)) : annihilatorSieve P Q₂ y ∈ J U := by
  refine J.transitive (Presheaf.imageSieve_mem J η y) _ fun V g hg ↦ ?_
  obtain ⟨t, ht⟩ := hg
  rw [annihilatorSieve_pullback, ← ht]
  refine J.superset_covering ?_ (h V t)
  rintro W k ⟨n, hn, hk⟩
  refine ⟨n, hn, ?_⟩
  rw [← NatTrans.naturality_apply η k.op, ← map_nsmul, hk, map_zero]

/-- A sheaf is locally annihilated along `P` exactly when the annihilator sieve of each of its
sections covers. -/
theorem locallyAnnihilated_iff (F : Sheaf J AddCommGrpCat.{w}) :
    LocallyAnnihilated J P F ↔ ∀ (U : C) (x : F.obj.obj (op U)), annihilatorSieve P F.obj x ∈ J U :=
  ⟨fun h U x ↦ by
    obtain ⟨R, hR, hk⟩ := h U x
    exact J.superset_covering (fun V f hf ↦ hk V f hf) hR,
    fun h U x ↦ ⟨_, h U x, fun _ _ hf ↦ hf⟩⟩

end Presheaf

section KanExtension

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {P : ℕ → Prop}

/-- **Local annihilation passes to a pointwise left Kan extension.** Let `G : C ⥤ D` be
cover-preserving and `Q` a presheaf of abelian groups on `C` all of whose sections are locally
annihilated along `P`, a predicate closed under products and satisfied by some integer. Then the
same holds for the left Kan extension of `Q` along `G.op`, if it is pointwise: its value at `U`
is the colimit of the values of `Q` over the arrows `U ⟶ G V`, hence generated by the
restrictions of the images of sections of `Q` (`CategoryTheory.Pretriangulated.mem_of_isColimit`),
and those are locally annihilated because `G` carries covering sieves to covering sieves. -/
theorem annihilatorSieve_mem_leftKanExtension (G : C ⥤ D) (hG : CoverPreserving J K G)
    (hP : ∃ n, P n) (hmul : ∀ m n, P m → P n → P (m * n)) (Q : Cᵒᵖ ⥤ AddCommGrpCat.{w})
    [G.op.HasPointwiseLeftKanExtension Q]
    (hQ : ∀ (V : C) (y : Q.obj (op V)), annihilatorSieve P Q y ∈ J V) (U : D)
    (x : (G.op.leftKanExtension Q).obj (op U)) :
    annihilatorSieve P (G.op.leftKanExtension Q) x ∈ K U := by
  let E := G.op.leftKanExtension Q
  let η := G.op.leftKanExtensionUnit Q
  have hη : ∀ (V : C) (y : Q.obj (op V)), annihilatorSieve P E (η.app (op V) y) ∈ K (G.obj V) := by
    intro V y
    refine K.superset_covering ?_ (hG.cover_preserve (hQ V y))
    rintro W h ⟨Z, g, h', ⟨n, hn, hz⟩, rfl⟩
    refine ⟨n, hn, ?_⟩
    have e : E.map (h' ≫ G.map g).op (η.app (op V) y) =
        E.map h'.op (η.app (op Z) (Q.map g.op y)) := by
      rw [NatTrans.naturality_apply η g.op y, op_comp, E.map_comp]
      rfl
    rw [e, ← map_nsmul, ← map_nsmul, hz, map_zero, map_zero]
  refine CategoryTheory.Pretriangulated.mem_of_isColimit
    (G.op.isPointwiseLeftKanExtensionLeftKanExtensionUnit Q (op U))
    (locallyAnnihilatedSubgroup K hP hmul U) (fun g y ↦ ?_) x
  have h := K.pullback_stable g.hom.unop (hη g.left.unop y)
  rw [annihilatorSieve_pullback] at h
  exact h

/-- **Local annihilation passes to inverse images of sheaves.** For a continuous functor `G` of
sites and a predicate `P` closed under products and satisfied by some integer, the inverse image
of a sheaf locally annihilated along `P`, constructed as a pointwise left Kan extension followed
by sheafification, is locally annihilated along `P`. -/
theorem locallyAnnihilated_sheafPullbackConstruction (G : C ⥤ D) [G.IsContinuous J K]
    [∀ F : Cᵒᵖ ⥤ AddCommGrpCat.{w}, G.op.HasPointwiseLeftKanExtension F]
    [HasWeakSheafify K AddCommGrpCat.{w}] [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (hP : ∃ n, P n) (hmul : ∀ m n, P m → P n → P (m * n)) (F : Sheaf J AddCommGrpCat.{w})
    (hF : LocallyAnnihilated J P F) :
    LocallyAnnihilated K P
      ((Functor.sheafPullbackConstruction.sheafPullback G AddCommGrpCat.{w} J K).obj F) := by
  rw [locallyAnnihilated_iff] at hF ⊢
  have key := annihilatorSieve_mem_of_isLocallySurjective (J := K) (P := P)
    (toSheafify K (G.op.lan.obj F.obj))
    (annihilatorSieve_mem_leftKanExtension G (CoverPreserving.of_isContinuous G J K) hP hmul
      F.obj hF)
  exact key

/-- **Local annihilation passes to quotient sheaves.** -/
theorem LocallyAnnihilated.of_epi [HasSheafify J AddCommGrpCat.{w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}] {F F' : Sheaf J AddCommGrpCat.{w}}
    (φ : F ⟶ F') [Epi φ] (h : LocallyAnnihilated J P F) : LocallyAnnihilated J P F' := by
  have : Sheaf.IsLocallySurjective φ :=
    (Sheaf.isLocallySurjective_iff_epi' (J := J) AddCommGrpCat φ).2 ‹_›
  rw [locallyAnnihilated_iff] at h ⊢
  exact annihilatorSieve_mem_of_isLocallySurjective φ.hom h

end KanExtension

section Torsion

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)

/-- Being `l`-power torsion is local annihilation along the positive powers of `l`. -/
theorem isPrimePowerTorsion_iff_locallyAnnihilated (l : ℕ) (F : Sheaf J AddCommGrpCat.{w}) :
    Stacks.Torsion.IsPrimePowerTorsion J l F ↔
      LocallyAnnihilated J (fun n ↦ ∃ r : ℕ, 0 < r ∧ n = l ^ r) F :=
  forall₂_congr fun _ _ ↦ exists_congr fun _ ↦ and_congr_right fun _ ↦
    forall₃_congr fun _ _ _ ↦
      ⟨fun ⟨r, hr, hn⟩ ↦ ⟨l ^ r, ⟨r, hr, rfl⟩, hn⟩, fun ⟨_, ⟨r, hr, rfl⟩, hn⟩ ↦ ⟨r, hr, hn⟩⟩

/-- Being torsion prime to `p` is local annihilation along the positive integers prime to `p`. -/
theorem isPrimeToCharacteristicTorsion_iff_locallyAnnihilated (p : ℕ)
    (F : Sheaf J AddCommGrpCat.{w}) :
    Stacks.Torsion.IsPrimeToCharacteristicTorsion J p F ↔
      LocallyAnnihilated J (fun n ↦ 0 < n ∧ n.Coprime p) F :=
  forall₂_congr fun _ _ ↦ exists_congr fun _ ↦ and_congr_right fun _ ↦
    forall₃_congr fun _ _ _ ↦ exists_congr fun _ ↦ and_assoc.symm

end Torsion

section Etale

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {P : ℕ → Prop}

/-- **Local annihilation passes to étale inverse images.** -/
theorem locallyAnnihilated_etaleAbelianInverseImage (hP : ∃ n, P n)
    (hmul : ∀ m n, P m → P n → P (m * n))
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (hG : LocallyAnnihilated Y.smallEtaleTopology P G) :
    LocallyAnnihilated X.smallEtaleTopology P ((etaleAbelianInverseImage.{u, v} f).obj G) :=
  locallyAnnihilated_sheafPullbackConstruction (smallEtaleBaseChange f) hP hmul G hG

/-- **Tag 04C9, the counit.** For an integral morphism `f`, the counit `f⁻¹ f_* F ⟶ F` of the
étale inverse-image/direct-image adjunction is an epimorphism. -/
theorem epi_etaleAbelianInverseImageDirectImageAdj_counit_app (hf : IsIntegralHom f)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    Epi ((etaleAbelianInverseImageDirectImageAdj.{u, 0} f).counit.app F) := by
  have : (etaleAbelianDirectImage.{u, 0} f).Faithful :=
    (smallEtalePushforwardAb_properties_of_isIntegralHom_or_locallyQuasiFinite f (Or.inl hf)).2.1
  infer_instance

/-- **Local annihilation descends along an integral direct image.** For an integral morphism
`f : X ⟶ Y` and a predicate `P` closed under products and satisfied by some integer, an abelian
sheaf `F` on `X_étale` is locally annihilated along `P` if `f_* F` is: `F` is a quotient of
`f⁻¹ f_* F` by Tag 04C9. -/
theorem locallyAnnihilated_of_directImage_of_isIntegralHom (hf : IsIntegralHom f)
    (hP : ∃ n, P n) (hmul : ∀ m n, P m → P n → P (m * n))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (h : LocallyAnnihilated Y.smallEtaleTopology P ((etaleAbelianDirectImage.{u, 0} f).obj F)) :
    LocallyAnnihilated X.smallEtaleTopology P F :=
  have := epi_etaleAbelianInverseImageDirectImageAdj_counit_app f hf F
  LocallyAnnihilated.of_epi ((etaleAbelianInverseImageDirectImageAdj.{u, 0} f).counit.app F)
    (locallyAnnihilated_etaleAbelianInverseImage.{u, 0} f hP hmul _ h)

/-- For an integral morphism `f`, an abelian sheaf `F` on `X_étale` is `l`-power torsion if
`f_* F` is. -/
theorem isPrimePowerTorsion_of_directImage (hf : IsIntegralHom f) {l : ℕ}
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (h : Stacks.Torsion.IsPrimePowerTorsion Y.smallEtaleTopology l
      ((etaleAbelianDirectImage.{u, 0} f).obj F)) :
    Stacks.Torsion.IsPrimePowerTorsion X.smallEtaleTopology l F := by
  rw [isPrimePowerTorsion_iff_locallyAnnihilated] at h ⊢
  refine locallyAnnihilated_of_directImage_of_isIntegralHom f hf ⟨l ^ 1, 1, one_pos, rfl⟩ ?_ F h
  rintro _ _ ⟨r, hr, rfl⟩ ⟨s, hs, rfl⟩
  exact ⟨r + s, by omega, (pow_add l r s).symm⟩

/-- For an integral morphism `f`, an abelian sheaf `F` on `X_étale` is torsion prime to `p` if
`f_* F` is. -/
theorem isPrimeToCharacteristicTorsion_of_directImage (hf : IsIntegralHom f) {p : ℕ}
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (h : Stacks.Torsion.IsPrimeToCharacteristicTorsion Y.smallEtaleTopology p
      ((etaleAbelianDirectImage.{u, 0} f).obj F)) :
    Stacks.Torsion.IsPrimeToCharacteristicTorsion X.smallEtaleTopology p F := by
  rw [isPrimeToCharacteristicTorsion_iff_locallyAnnihilated] at h ⊢
  exact locallyAnnihilated_of_directImage_of_isIntegralHom f hf
    ⟨1, one_pos, Nat.coprime_one_left p⟩
    (fun m n ⟨hm, hm'⟩ ⟨hn, hn'⟩ ↦ ⟨Nat.mul_pos hm hn, Nat.coprime_mul_iff_left.2 ⟨hm', hn'⟩⟩) F h

end Etale

end Stacks.EtaleCohomology

end
